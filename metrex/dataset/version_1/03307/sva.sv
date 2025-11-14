// SVA for Comparator — concise, full functional checks and coverage
// Bind-in module (no clock needed; uses immediate assertions in always_comb)

module Comparator_sva #(parameter int n = 4)
(
  input  logic [n-1:0] in1,
  input  logic [n-1:0] in2,
  input  logic [1:0]   out
);

  localparam logic [n-1:0] MIN = '0;
  localparam logic [n-1:0] MAX = {n{1'b1}};

  // Core functional checks and X/encoding guards
  always_comb begin
    // Output encoding valid and 2-state
    assert (out inside {2'b00, 2'b01, 2'b10})
      else $error("Comparator: illegal out encoding: %b", out);
    assert (!$isunknown(out))
      else $error("Comparator: out has X/Z: %b", out);

    // Inputs 2-state (catch X/Z driving misleading path)
    assert (!$isunknown(in1) && !$isunknown(in2))
      else $error("Comparator: inputs have X/Z: in1=%b in2=%b", in1, in2);

    // Functional correctness (complete and mutually exclusive mapping)
    assert ( (out==2'b01 && (in1 >  in2)) ||
             (out==2'b00 && (in1 == in2)) ||
             (out==2'b10 && (in1 <  in2)) )
      else $error("Comparator mismatch: in1=%0d in2=%0d out=%b", in1, in2, out);
  end

  // Compact functional coverage
  always_comb begin
    // Main relations
    cover (in1 >  in2 && out == 2'b01);
    cover (in1 == in2 && out == 2'b00);
    cover (in1 <  in2 && out == 2'b10);

    // Boundary conditions
    cover (in1==MIN && in2==MAX && out==2'b10);
    cover (in1==MAX && in2==MIN && out==2'b01);
    cover (in1==MIN && in2==MIN && out==2'b00);
    cover (in1==MAX && in2==MAX && out==2'b00);

    // Off-by-one cases
    cover (in1 == in2 + 1 && out==2'b01);
    cover (in2 == in1 + 1 && out==2'b10);
  end

endmodule

// Bind to DUT
bind Comparator Comparator_sva #(.n(n)) comparator_sva_i (.in1(in1), .in2(in2), .out(out));