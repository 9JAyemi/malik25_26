// SVA checker for mux_min_xor
// Bind this module to the DUT and connect a sampling clock from your TB.

module mux_min_xor_sva (
  input logic                  clk,
  input logic [2:0]            sel,
  input logic [3:0]            data0, data1, data2, data3, data4, data5,
  input logic [7:0]            a, b, c, d,
  input logic [7:0]            out
);

  default clocking cb @(posedge clk); endclocking

  // Recreate RTL behavior (including width/concat truncation)
  function automatic logic [3:0] f_mux (logic [2:0] s,
                                        logic [3:0] d0,d1,d2,d3,d4,d5);
    case (s)
      3'b000: return d0;
      3'b001: return d1;
      3'b010: return d2;
      3'b011: return d3;
      3'b100: return d4;
      3'b101: return d5;
      default: return 4'b0000;
    endcase
  endfunction

  function automatic logic [7:0] f_min_out (logic [7:0] a,b,c,d);
    logic [6:0] min_cd, min_bd;
    min_cd = (c[6:0] < d[6:0]) ? c[6:0] : d[6:0];
    min_bd = (b[6:0] < d[6:0]) ? b[6:0] : d[6:0];
    return {min_bd[0], min_cd}; // matches RHS concat truncation in RTL
  endfunction

  logic [3:0] exp_mux;
  logic [7:0] exp_min, exp_out;

  always_comb begin
    exp_mux = f_mux(sel, data0,data1,data2,data3,data4,data5);
    exp_min = f_min_out(a,b,c,d);
    exp_out = exp_min ^ {4'b0000, exp_mux};
  end

  // Basic X checks (can be relaxed/disabled if needed)
  a_no_x_inputs: assert property (!$isunknown({sel,data0,data1,data2,data3,data4,data5,a,b,c,d})))
    else $error("mux_min_xor: X/Z on inputs");

  // Golden functional check: out equals mux^min (with zero-extend of mux)
  a_out_correct: assert property (out == exp_out)
    else $error("mux_min_xor: out mismatch exp_out=%0h out=%0h", exp_out, out);

  // Structural sanity: upper nibble passes min_out, lower nibble XORs with mux
  a_upper_passthru: assert property (out[7:4] == exp_min[7:4])
    else $error("mux_min_xor: upper nibble mismatch");
  a_lower_xor: assert property (out[3:0] == (exp_min[3:0] ^ exp_mux))
    else $error("mux_min_xor: lower nibble mismatch");

  // When sel is outside 0..5, mux is 0, so out == min_out
  a_invalid_sel_passthru: assert property ((sel inside {3'b110,3'b111}) |-> (out == exp_min))
    else $error("mux_min_xor: invalid sel not passing through min_out");

  // Minimal but targeted functional coverage
  c_sel_all:       cover property (sel inside {3'b000,3'b001,3'b010,3'b011,3'b100,3'b101,3'b110,3'b111});
  c_cd_lt:         cover property ((c[6:0] < d[6:0]));
  c_cd_ge:         cover property (!(c[6:0] < d[6:0]));
  c_bd_bit_min0:   cover property (({b[0],d[0]} inside {2'b01,2'b10})); // min bit = 0 due to one 0
  c_bd_bit_min1:   cover property ((b[0] & d[0]));                      // min bit = 1 only if both 1
  c_passthru_inv:  cover property ((sel inside {3'b110,3'b111}) && (out == exp_min));

endmodule

// Example bind (connect your TB clock)
// bind mux_min_xor mux_min_xor_sva u_mux_min_xor_sva (.* , .clk(tb_clk));