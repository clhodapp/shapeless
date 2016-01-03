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

trait Upcast[T] {
  type P
  def upcast(t: T): P
}
object Upcast {
  type Aux[T, P0] = Upcast[T] { type P = P0 }
  def apply[T](implicit t: Upcast[T]): Aux[T, t.P] = t
  implicit def upcast[T]: Upcast[T] = macro upcastImpl[T]
  def upcastImpl[T: c.WeakTypeTag](c: whitebox.Context): c.Tree = {
    import c.universe._
    val tpe = weakTypeOf[T]
    val baseTypes = (tpe match {
      case RefinedType(b, _) => b
      case other => weakTypeOf[T].baseClasses.map(tpe.baseType(_))
    }).map(TypeTree(_))
    val parentType = baseTypes.tail.reduceOption[Tree]((a, b) => tq"$a with $b").getOrElse(tq"Any")
    val nme = TermName(c.freshName("upcast"))
    q"""
      new _root_.shapeless.Upcast[$tpe] {
        type P = $parentType
        def upcast($nme: $tpe): P = $nme
      }: Upcast.Aux[$tpe, $parentType]
    """
  }
}
