open Js_of_ocaml

let () =
  Js.export "whatevs" begin
    object%js
      method add x y = x +. y
      val zero = 0.
    end
  end

