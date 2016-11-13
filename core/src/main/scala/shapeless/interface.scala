/*
 * Copyright (c) 2016 Miles Sabin
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package shapeless

import scala.language.experimental.macros

import scala.reflect.macros.whitebox

trait Interface[T] extends Serializable {
  type Repr
  def to(t : T) : Repr
  def from(r: Repr): T
}

object Interface {
  type Aux[T, Repr0] = Interface[T] { type Repr = Repr0 }
  def apply[T](implicit iface: Interface[T]): Aux[T, iface.Repr] = iface
  implicit def materialize[T, R]: Interface.Aux[T, R] =
    macro InterfaceMacros.materializeUnlabelledInterface[T, R]
}

trait FlattenHList[Nested <: HList] {
  type Flattened <: HList
  def flatten(nested: Nested): Flattened
  def nest(flat: Flattened): Nested
}
object FlattenHList {

  import shapeless.ops.hlist._

  type Aux[Nested <: HList, Flattened0 <: HList] = FlattenHList[Nested] {
    type Flattened = Flattened0
  }

  def apply[N <: HList](implicit fhl: FlattenHList[N]): Aux[N, fhl.Flattened] = fhl

  implicit val hnilInstance: FlattenHList.Aux[HNil, HNil] = {
    new FlattenHList[HNil] {
      type Flattened = HNil
      def flatten(hnil: HNil) = hnil
      def nest(hnil: HNil) = hnil
    }
  }

  implicit def hconsInstance[
    H <: HList, Len <: Nat, T <: HList, FT <: HList, Flattened0 <: HList
  ](implicit
    len: Length.Aux[H, Len],
    flattenT: FlattenHList.Aux[T, FT],
    prepend: Prepend.Aux[H, FT, Flattened0],
    split: Split.Aux[Flattened0, Len, H, FT]
  ): FlattenHList.Aux[H :: T, Flattened0] =
    new FlattenHList[H :: T] {
      type Flattened = Flattened0
      def flatten(nested: H :: T) = {
        prepend(
          nested.head,
          flattenT.flatten(nested.tail)
        )
      }
      def nest(flattened: Flattened) = {
        val (h, t) = split(flattened)
        h :: flattenT.nest(t)
      }
    }

}

trait FlattenParamList[Nested] {
  type Flattened
  def flatten(nested: Nested): Flattened
  def nest(flat: Flattened): Nested
}
object FlattenParamList {

  type Aux[Nested, Flattened0] = FlattenParamList[Nested] {
    type Flattened = Flattened0
  }

  def apply[N](implicit fpl: FlattenParamList[N]): Aux[N, fpl.Flattened] = fpl

  implicit def instance[N <: HList, F <: HList, R](implicit
    fpl: FlattenHList.Aux[N, F]
  ): FlattenParamList.Aux[N => R, F => R] = new FlattenParamList[N => R]{
    type Flattened = F => R
    def flatten(nested: N => R): F => R = f => nested(fpl.nest(f))
    def nest(flattened: F => R): N => R = n => flattened(fpl.flatten(n))
  }

}

trait FlattenParamLists[Nested] extends Serializable {
  type Flattened
  def flatten(nested: Nested): Flattened
  def nest(flattened: Flattened): Nested
}
object FlattenParamLists {

  type Aux[Nested, Flattened0] =
    FlattenParamLists[Nested] { type Flattened = Flattened0 }

  def apply[T](implicit fpl: FlattenParamLists[T]): Aux[T, fpl.Flattened] = fpl

  implicit val hnilInstance: FlattenParamLists.Aux[HNil, HNil] = {
    new FlattenParamLists[HNil] {
      type Flattened = HNil
      def flatten(hnil: HNil): HNil = hnil
      def nest(hnil: HNil): HNil = hnil
    }
  }

  implicit def hconsInstance[H, FH, T <: HList, FT <: HList](implicit
    flattenHead: FlattenParamList.Aux[H, FH],
    flattenTail: FlattenParamLists.Aux[T, FT]
  ): FlattenParamLists.Aux[H :: T, FH :: FT] = {
    new FlattenParamLists[H :: T] {
      type Flattened = FH :: FT
      def flatten(nested: H :: T) = {
        flattenHead.flatten(nested.head) :: flattenTail.flatten(nested.tail)
      }
      def nest(flattened: FH :: FT) = {
        flattenHead.nest(flattened.head) :: flattenTail.nest(flattened.tail)
      }
    }
  }
}


@macrocompat.bundle
class InterfaceMacros(val c: whitebox.Context) extends SingletonTypeUtils {

  import c.universe._
  import compat._

  case class InterfaceInfo(members: List[MemberInfo])
  case class MemberInfo(
    name: TermName,
    paramLists: List[List[ParamInfo]],
    returnType: Tree
  )
  case class ParamInfo(
    name: TermName,
    paramType: Tree
  )

  sealed trait ExtractionError
  case class NotTrait(tpe: Type) extends ExtractionError
  case class ConcreteMember(symbol: Symbol) extends ExtractionError
  case class GenericMember(symbol: Symbol) extends ExtractionError
  case class ByNameParameter(param: Symbol) extends ExtractionError

  def traverse[T](
    items: List[Either[ExtractionError, T]]
  ): Either[ExtractionError, List[T]] = {
    items.foldRight[Either[ExtractionError, List[T]]](Right(Nil)) {
      case (Right(added), Right(current)) => Right(added :: current)
      case (Right(ignored), Left(existingErr)) => Left(existingErr)
      case (Left(newErr), dropped) => Left(newErr)
    }
  }

  val defaultBaseTypeSymbols = {
    Set[Symbol](
      symbolOf[Any],
      symbolOf[AnyRef],
      symbolOf[AnyVal],
      symbolOf[Object]
    )
  }

  implicit class BiasEither[T](e: Either[ExtractionError, T]) {
    def map[U](
      f: T => U
    ): Either[ExtractionError, U] = {
      e.right.map(f)
    }
    def flatMap[U](
      f: T => Either[ExtractionError, U]
    ): Either[ExtractionError, U] = {
      e.right.flatMap(f)
    }
  }

  def extractInterfaceInfo(
    tpe: Type
  ): Either[ExtractionError, InterfaceInfo] = {
    for {
      memberSymbols <- {
        if (tpe.typeSymbol.isClass && tpe.typeSymbol.asClass.isTrait) Right {
          tpe
            .members
            .flatMap(_.alternatives)
            .filterNot(member => defaultBaseTypeSymbols contains member.owner)
            .toList
        } else Left(NotTrait(tpe))
      }
      members <- traverse {
        memberSymbols.map(extractMemberInfo(tpe))
      }
    } yield InterfaceInfo(members = members)
  }

  def extractMemberInfo(
    containingType: Type
  )(
    memberSymbol: Symbol
  ): Either[ExtractionError, MemberInfo] = {
    for {
      signature <- {
          val signature = memberSymbol.typeSignatureIn(containingType)
          if (!memberSymbol.isAbstract) Left(ConcreteMember(memberSymbol))
          else if (signature.typeParams.nonEmpty) Left(GenericMember(memberSymbol))
          else Right(signature)
      }
      name <- Right(memberSymbol.name.toTermName)
      returnType <- Right(TypeTree(signature.finalResultType))
      paramLists <- traverse {
        signature.paramLists.map { paramList =>
          traverse {
            paramList.map(extractParamInfo(signature))
          }
        }
      }
    } yield MemberInfo(name = name, returnType = returnType, paramLists = paramLists)
  }

  def extractParamInfo(
    methodSignature: Type
  )(
    paramSymbol: Symbol
  ): Either[ExtractionError, ParamInfo] = {
    for {
      paramType <- {
        if (paramSymbol.asTerm.isByNameParam) Left(ByNameParameter(paramSymbol))
        else Right(TypeTree(paramSymbol.typeSignatureIn(methodSignature)))
      }
      name <- Right(paramSymbol.name.toTermName)
    } yield ParamInfo(name = name, paramType = paramType)
  }

  def tpeHCons(a: Tree, b: Tree): Tree = tq"_root_.shapeless.::[$a, $b]"
  val tpeHNil: Tree = tq"_root_.shapeless.HNil"

  def valueHCons(a: Tree, b: Tree): Tree = q"_root_.shapeless.::($a, $b)"
  val valueHNil: Tree = q"_root_.shapeless.HNil"

  def materializeInterface[T: WeakTypeTag, R: WeakTypeTag](
    typeclassName: String,
    paramRepr: ParamInfo => Tree,
    functionRepr: TermName => Tree => Tree
  ): Tree = {

    extractInterfaceInfo(weakTypeOf[T]) match {
      case Left(NotTrait(nonTrait)) =>
        if (c.compilerSettings contains "-Xlog-implicits") {
          c.error(
            nonTrait.typeSymbol.pos,
            "Note: unsupported non-trait defined here"
          )
        } else ()
        c.abort(
          c.enclosingPosition,
          "Unsupported Type: Interface-type generic represenation converters can only be generated for traits"
        )
      case Left(ByNameParameter(byNameParam)) =>
        if (c.compilerSettings contains "-Xlog-implicits") {
          c.error(
            byNameParam.pos,
            "Note: unsupported by-name parameter defined here"
          )
        } else ()
        c.abort(
          c.enclosingPosition,
          "Unsupported Type: Interface-type generic represenation converters can only be generated for interfaces when none of their member methods have by-name parameters"
        )
      case Left(GenericMember(genericMember)) =>
        if (c.compilerSettings contains "-Xlog-implicits") {
          c.error(
            genericMember.pos,
            "Note: unsupported generic member defined here"
          )
        } else ()
        c.abort(
          c.enclosingPosition,
          "Unsupported Type: Interface-type generic represenation converters can only be generated for traits with no generic members"
        )
      case Left(ConcreteMember(concreteMember)) =>
        if (c.compilerSettings contains "-Xlog-implicits") {
          c.error(
            concreteMember.pos,
            "Note: unsupported concrete member defined here"
          )
        } else ()
        c.abort(
          c.enclosingPosition,
          "Unsupported Type: Interface-type generic represenation converters can only be generated for traits with no concrete members"
        )
      case Right(interfaceInfo) =>
        val reprTypeTree = {
          interfaceInfo.members.map {
            case MemberInfo(name, paramLists, returnType) =>
              val unifiedParamLists = {
                paramLists
                  .map(_.map(paramRepr).foldRight(tpeHNil)(tpeHCons))
                  .foldRight(tpeHNil)(tpeHCons)
              }
              functionRepr(name)(tq"$unifiedParamLists => $returnType")
          }.foldRight(tpeHNil)(tpeHCons)
        }
        val toGeneric = {
          val target = TermName(c.freshName("target"))
            val body = interfaceInfo.members.map {
              case MemberInfo(name, paramLists, returnType) =>
                val param = Ident(TermName(c.freshName("param")))
                val arguments = {
                  paramLists
                    .zipWithIndex
                    .map { case (paramList, listIndex) =>
                      paramList.zipWithIndex.map { case (name, paramIndex) =>
                        q"$param.apply($listIndex).apply($paramIndex)" }
                    }
                }
                val paramType = {
                  paramLists
                    .map(_.map(paramRepr).foldRight(tpeHNil)(tpeHCons))
                    .foldRight(tpeHNil)(tpeHCons)
                }
                val application = q"${target}.${name}(...${arguments})"
                val functionType = functionRepr(name)(tq"$paramType => $returnType")
                q"{ ($param: $paramType) => $application }.asInstanceOf[$functionType]"
            }.foldRight(valueHNil)(valueHCons)
            q"""
              val $target = t
              $body
            """
        }
        val toConcrete = {
          val target = TermName(c.freshName("target"))
          val members = interfaceInfo.members.zipWithIndex.map {
            case (MemberInfo(name, paramLists, returnType), idx) =>
              val body = {
                val arg =
                  paramLists
                    .map { paramList =>
                      paramList.map { param =>
                        val paramReprTpe = paramRepr(param)
                        q"${param.name}.asInstanceOf[$paramReprTpe]"
                      }.foldRight(valueHNil)(valueHCons)
                    }.foldRight(valueHNil)(valueHCons)
                q"$target.apply($idx).apply($arg)"
              }
              val parameters = paramLists.map { paramList =>
                paramList.map { param =>
                  q"${param.name}: ${param.paramType}"
                }
              }
              q"""def $name(...$parameters) = $body"""
          }
          q"""
            val $target = r
            new ${weakTypeOf[T]} {
              ..$members
            }
          """
        }
        val tpeNme = TypeName(typeclassName)
        q"""
          new _root_.shapeless.$tpeNme[${weakTypeOf[T]}] {
            type Repr = ${reprTypeTree}
            def to(t: ${weakTypeOf[T]}): ${reprTypeTree} = $toGeneric
            def from(r: ${reprTypeTree}): ${weakTypeOf[T]} = $toConcrete
          }
        """
    }

  }

  def materializeUnlabelledInterface[T: WeakTypeTag, R: WeakTypeTag]: Tree = {
    def unlabelledParam(paramInfo: ParamInfo): Tree = paramInfo.paramType
    def unlabelledFunction(name: TermName): Tree => Tree = identity
    materializeInterface[T, R]("Interface", unlabelledParam, unlabelledFunction)
  }

  def materializeLabelledInterface[T: WeakTypeTag, R: WeakTypeTag]: Tree = {
    def labelledParam(paramInfo: ParamInfo): Tree = {
      val paramType = paramInfo.paramType
      val paramNameTree = SingletonSymbolType(paramInfo.name.decodedName.toString)
      tq"_root_.shapeless.labelled.FieldType[$paramNameTree, $paramType]"
    }
    def labelledFunction(functionName: TermName): Tree => Tree = { functionTree =>
      val functionNameTree = SingletonSymbolType(functionName.decodedName.toString)
      tq"_root_.shapeless.labelled.FieldType[$functionNameTree, $functionTree]"
    }
    materializeInterface[T, R]("LabelledInterface", labelledParam, labelledFunction)
  }

}

trait LabelledInterface[T] extends Serializable {
  type Repr
  def to(t : T) : Repr
  def from(r: Repr): T
}

object LabelledInterface {
  type Aux[T, Repr0] = LabelledInterface[T] { type Repr = Repr0 }
  def apply[T](implicit iface: LabelledInterface[T]): Aux[T, iface.Repr] = iface
  implicit def materialize[T, R]: LabelledInterface.Aux[T, R] =
    macro InterfaceMacros.materializeLabelledInterface[T, R]
}
