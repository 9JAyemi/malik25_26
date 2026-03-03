// SVA for add2_and_round and add2_and_round_reg (concise, high-quality checks + coverage)

package add2_and_round_sva_pkg;

  // Reference function (end-around carry)
  function automatic [W-1:0] exp_sum #(int W) (input logic [W-1:0] a, b);
    logic [W:0] s;
    begin
      s       = a + b;
      exp_sum = s[W-1:0] + s[W];
    end
  endfunction

  // Combinational module SVA
  module add2_and_round_sva #(parameter int WIDTH=16)
    (input logic [WIDTH-1:0] in1, in2, sum);

    // Knownness + functional equivalence (immediate checks for comb)
    always_comb begin
      assert (!$isunknown({in1,in2,sum}))
        else $error("add2_and_round: X/Z on inputs or output");
      assert (sum === exp_sum#(WIDTH)(in1,in2))
        else $error("add2_and_round: sum mismatch in1=%0h in2=%0h sum=%0h exp=%0h",
                    in1,in2,sum,exp_sum#(WIDTH)(in1,in2));

      // sum==0 iff both inputs are 0 (given end-around carry)
      assert ((sum=={WIDTH{1'b0}}) == ((in1=={WIDTH{1'b0}})&&(in2=={WIDTH{1'b0}})))
        else $error("add2_and_round: zero result condition violated");

      // Coverage (immediate cover)
      logic [WIDTH:0] s;
      s = in1 + in2;
      cover (s[WIDTH]==1'b0); // no carry
      cover (s[WIDTH]==1'b1); // carry (end-around increment active)
      cover (in1=={WIDTH{1'b0}} && in2=={WIDTH{1'b0}});
      cover (in1=={WIDTH{1'b1}} && in2=={WIDTH{1'b1}});
    end
  endmodule

  // Registered module SVA
  module add2_and_round_reg_sva #(parameter int WIDTH=16)
    (input logic clk,
     input logic [WIDTH-1:0] in1, in2,
     input logic [WIDTH-1:0] sum);

    let s = in1 + in2;

    // Knownness at sampling edge
    assert property (@(posedge clk) !$isunknown({clk,in1,in2,sum}));

    // Correct registered value (same-cycle compute, 1-cycle register)
    assert property (@(posedge clk) sum == exp_sum#(WIDTH)(in1,in2));

    // Split by carry (clarity; redundant with the main check but helpful)
    assert property (@(posedge clk) (s[WIDTH]==1'b0) |-> (sum == s[WIDTH-1:0]));
    assert property (@(posedge clk) (s[WIDTH]==1'b1) |-> (sum == (s[WIDTH-1:0] + 1'b1)));

    // sum==0 iff both inputs are 0 (under this arithmetic)
    assert property (@(posedge clk)
                     (sum=={WIDTH{1'b0}}) == ((in1=={WIDTH{1'b0}})&&(in2=={WIDTH{1'b0}})));

    // Coverage
    cover property (@(posedge clk) s[WIDTH]==1'b0);
    cover property (@(posedge clk) s[WIDTH]==1'b1);
    cover property (@(posedge clk) in1=={WIDTH{1'b0}} && in2=={WIDTH{1'b0}});
    cover property (@(posedge clk) in1=={WIDTH{1'b1}} && in2=={WIDTH{1'b1}});
  endmodule

endpackage

// Bind SVA to DUTs
import add2_and_round_sva_pkg::*;

bind add2_and_round
  add2_and_round_sva #(.WIDTH(WIDTH))
    add2_and_round_sva_i (.in1(in1), .in2(in2), .sum(sum));

bind add2_and_round_reg
  add2_and_round_reg_sva #(.WIDTH(WIDTH))
    add2_and_round_reg_sva_i (.clk(clk), .in1(in1), .in2(in2), .sum(sum));