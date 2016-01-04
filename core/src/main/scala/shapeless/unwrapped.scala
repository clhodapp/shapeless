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

import newtype._

import language.experimental.macros
import reflect.macros.whitebox

class UnwrappedMacros(val c: whitebox.Context) extends CaseClassMacros {
  import c.universe._

  def mkUnwrapSelf[T: WeakTypeTag]: Tree = {
    val tpe = weakTypeOf[T]
    q"_root_.shapeless.Unwrapped.TheMacroSelfUnwrapped.asInstanceOf[_root_.shapeless.Unwrapped.MacroSelfUnwrapped[$tpe]]"
  }
  def identity[T](t: Tree): Tree = t

  def mkUnwrapAnyVal[W <: AnyVal : WeakTypeTag]: Tree = {
    val wTpe = weakTypeOf[W]
    // For some reason, the compiler doesn't seem to respect
    // the AnyVal bound on the parameter and calls this macro
    // with things like String... Seems like a bug...
    if (!(wTpe <:< typeOf[AnyVal])) abort("not an AnyVal")
    val fields = fieldsOf(wTpe)
    if (fields.isEmpty) q"new _root_.shapeless.Unwrapped.MacroSelfUnwrapped[$wTpe]"
    else {
      val wrapped = fields.head._1
      val uTpe = fields.head._2
      val wParam = TermName(c.freshName("w"))
      val uParam = TermName(c.freshName("u"))
      val chainTpe = appliedType(typeOf[Unwrapped[_]].typeConstructor, uTpe)
      val chain = c.inferImplicitValue(chainTpe, silent = true)
      val ufTpe = chain.tpe.member(TypeName("U")).typeSignatureIn(chain.tpe)
      q"""
        new _root_.shapeless.Unwrapped.MacroAnyValUnwrapped[$wTpe, $uTpe, $ufTpe](
          ($wParam: $wTpe) => $chain.unwrap($wParam.$wrapped),
          ($uParam: $ufTpe) => new $wTpe($chain.wrap($uParam))
        )
      """
    }
  }
  def unwrapAnyVal[W <: AnyVal: WeakTypeTag, U: WeakTypeTag](w: Tree): Tree = {
    val wTpe = weakTypeOf[W]
    val uTpe = weakTypeOf[U]
    val fields = fieldsOf(wTpe)
    val wrapped = fields.head._1
    q"_root_.shapeless.the[_root_.shapeless.Unwrapped[$uTpe]].unwrap($w.$wrapped)"
  }
  def wrapAnyVal[W <: AnyVal: WeakTypeTag, U: WeakTypeTag](u: Tree): Tree = {
    val wTpe = weakTypeOf[W]
    val uTpe = weakTypeOf[U]
    val fields = fieldsOf(wTpe)
    q"new $wTpe(_root_.shapeless.the[_root_.shapeless.Unwrapped[$uTpe]].wrap($u))"
  }

  def mkUnwrapNewtype[Repr: WeakTypeTag, Ops: WeakTypeTag]: Tree = {
    val wTpe = weakTypeOf[Newtype[Repr, Ops]]
    val uTpe = weakTypeOf[Repr]
    val wParam = TermName(c.freshName("w"))
    val uParam = TermName(c.freshName("u"))
    val chainTpe = appliedType(typeOf[Unwrapped[_]].typeConstructor, uTpe)
    val chain = c.inferImplicitValue(chainTpe, silent = true)
    val ufTpe = chain.tpe.member(TypeName("U")).typeSignatureIn(chain.tpe)
    q"""
      new _root_.shapeless.Unwrapped.MacroNewtypeUnwrapped[$wTpe, $uTpe, $ufTpe](
        ($wParam: $wTpe) => $chain.unwrap($wParam.asInstanceOf[$uTpe]),
        ($uParam: $ufTpe) => $chain.wrap($uParam).asInstanceOf[$wTpe]
      )
    """
  }
  def unwrapNewtype[W: WeakTypeTag, U: WeakTypeTag](w: Tree): Tree = {
    val wTpe = weakTypeOf[W]
    val uTpe = weakTypeOf[U]
    val fields = fieldsOf(wTpe)
    q"_root_.shapeless.the[_root_.shapeless.Unwrapped[$uTpe]].unwrap($w.asInstanceOf[$uTpe])"
  }
  def wrapNewtype[W: WeakTypeTag, U: WeakTypeTag](u: Tree): Tree = {
    val wTpe = weakTypeOf[W]
    val uTpe = weakTypeOf[U]
    q"_root_.shapeless.the[_root_.shapeless.Unwrapped[$uTpe]].wrap($u).asInstanceOf[$wTpe]"
  }

  def unwrap(uw: Tree): Tree = q"$uw.unwrap(${c.prefix}.t)"
  def wrap(uw: Tree): Tree = q"$uw.wrap(${c.prefix}.t)"
}

trait Unwrapped[W] extends Serializable {
  type U
  def unwrap(w: W): U
  def wrap(u: U): W
}

object Unwrapped extends UnwrappedInstances {
  type Aux[W, U0] = Unwrapped[W] { type U = U0 }
  def apply[W](implicit w: Unwrapped[W]): Aux[W, w.U] = w


  class ConcreteUnwrapped[W, U0](
    u: W => U0,
    w: U0 => W
  ) extends Unwrapped[W] {
    type U = U0
    def unwrap(w: W): U = u(w)
    def wrap(u: U): W = w(u)
  }
  object TheConcreteSelfUnwrapped extends ConcreteUnwrapped[Any, Any](
    identity,
    identity
  )

  class IdentityUnwrapped[T] extends ConcreteUnwrapped[T, T](
    identity,
    identity
  ) {
    override def unwrap(t: T): T = macro UnwrappedMacros.identity[T]
    override def wrap(t: T): T = macro UnwrappedMacros.identity[T]
  }
  object IdentityUnwrapped extends IdentityUnwrapped[Any]


  class AnyValUnwrapped[W <: AnyVal, UI, UF](
    u: W => UF,
    w: UF => W
  ) extends ConcreteUnwrapped[W, UF](u, w) {
    override def unwrap(w: W): UF = macro UnwrappedMacros.unwrapAnyVal[W, UI]
    override def wrap(u: U): W = macro UnwrappedMacros.wrapAnyVal[W, UI]
  }

}

trait UnwrappedInstances extends LowPriorityUnwrappedInstances {

  implicit def unwrapAnyVal[W <: AnyVal, T]: Unwrapped.Aux[W, T] =
    macro UnwrappedMacros.mkUnwrapAnyVal[W]
  implicit def unwrapNewtype[Repr, Ops]: Unwrapped[Newtype[Repr, Ops]] =
    macro UnwrappedMacros.mkUnwrapNewtype[Repr, Ops]

}

trait LowPriorityUnwrappedInstances {
  implicit def selfUnwrapped[T]: Unwrapped.Aux[T, T] = macro UnwrappedMacros.mkUnwrapSelf[T]
}
