/*
 * Copyright 2024 The STARS Project Authors
 * SPDX-License-Identifier: Apache-2.0
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

package tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation

interface ObjectReference

class Ref(val id: Int, val ref: SmtTranslatable) : ObjectReference

class Val<T>(val value: T) : ObjectReference

class Lst<T>(val id: Int, val list: Collection<T>) : ObjectReference

class RefLst(val id: Int, val list: Collection<SmtTranslatable>) : ObjectReference

class Enm(val value: Any) : ObjectReference

class Nll() : ObjectReference

class ObjectRepresentation(val ref: Any, val member: Map<String, ObjectReference>)
