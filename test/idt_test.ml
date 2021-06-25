open OUnit2
open Profint

let clone str = String.(init (length str) (get str))

let tests =
  "Idt" >::: [
    "(intern hello) == (intern hello)" >:: begin fun _cx ->
      let str1 = clone "hello" in
      let str2 = clone "hello" in
      assert_equal ~cmp:(==) Idt.(intern str1) Idt.(intern str2)
    end ;
    "(intern hello) != (intern bonjour)" >:: begin fun _cx ->
      let str1 = clone "hello" in
      let str2 = clone "bonjour" in
      assert_equal ~cmp:(!=) Idt.(intern str1) Idt.(intern str2)
    end ;
    "(intern str).str == str" >:: begin fun _cx ->
      let str = clone "hello" in
      assert_equal ~cmp:(==) Idt.((intern str).str) str
    end ;
  ]
