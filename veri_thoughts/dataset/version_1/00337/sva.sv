// SVA for karnaugh_map
module karnaugh_map_sva (
  input  logic [3:0] x,
  input  logic       f,
  input  logic       d1, d2, d3, d4
);
  logic exp_d1, exp_d2, exp_d3, exp_d4;
  logic exp_f_or, exp_f_fact;

  always_comb begin
    exp_d1 = x[0] & x[1];
    exp_d2 = x[0] & x[2];
    exp_d3 = x[1] & x[3];
    exp_d4 = x[2] & x[3];
    exp_f_or   = d1 | d2 | d3 | d4;
    exp_f_fact = (x[1] | x[2]) & (x[0] | x[3]);

    if (!$isunknown(x)) begin
      assert (d1 == exp_d1) else $error("karnaugh_map: d1 mismatch");
      assert (d2 == exp_d2) else $error("karnaugh_map: d2 mismatch");
      assert (d3 == exp_d3) else $error("karnaugh_map: d3 mismatch");
      assert (d4 == exp_d4) else $error("karnaugh_map: d4 mismatch");

      assert (f == exp_f_or)   else $error("karnaugh_map: f != d1|d2|d3|d4");
      assert (f == exp_f_fact) else $error("karnaugh_map: f != (x1|x2)&(x0|x3)");

      assert (!$isunknown({d1,d2,d3,d4,f}))
        else $error("karnaugh_map: X/Z on internal/output with 2-state inputs");
    end
  end

  // Functional coverage: all 16 input combinations; observe f=0 and f=1; each di asserted at least once
  generate
    for (genvar i = 0; i < 16; i++) begin : C_X
      localparam logic [3:0] V = i;
      always_comb cover (x == V);
    end
  endgenerate
  always_comb begin
    cover (f == 1'b0);
    cover (f == 1'b1);
    cover (d1);
    cover (d2);
    cover (d3);
    cover (d4);
  end
endmodule

bind karnaugh_map karnaugh_map_sva kmap_sva_b (.*);