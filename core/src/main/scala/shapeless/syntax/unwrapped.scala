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
package syntax

import language.experimental.macros

object unwrapped {
  class UnwrappedSyntax[T](val t: T) {
    def unwrap[U](implicit uw: Unwrapped.Aux[T, U]): U = macro UnwrappedMacros.unwrap
    def wrap[U](implicit uw: Unwrapped.Aux[U, T]): U = macro UnwrappedMacros.wrap
  }
  implicit def unwrappedSyntax[T](t: T) = null: UnwrappedSyntax[T]
}
