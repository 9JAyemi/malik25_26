// SVA package with compact reference models
package top_checks_pkg;
  // 4b rotate-right by 1 when sel=1, else rotate-left by 2; zero-extend to 5b (matches DUT width behavior)
  function automatic logic [4:0] shift_ref(logic [3:0] din, logic sel);
    shift_ref = {1'b0, sel ? {din[3], din[2:0]} : {din[1:0], din[3:2]}};
  endfunction

  // Next strictly-larger power-of-two (saturate to 16). For x==0, returns 1.
  function automatic logic [4:0] next_pow2_strict(logic [4:0] x);
    logic [4:0] y;
    if (x <= 5'd1) begin
      y = 5'd1;
    end else begin
      y = x - 5'd1;
      y |= (y >> 1);
      y |= (y >> 2);
      y |= (y >> 4);
      y = y + 5'd1;            // round up to power-of-two >= x
      if ((y == x) && (y != 5'd16)) y = y << 1; // strictly larger if already power-of-two, except at 16
    end
    next_pow2_strict = (y > 5'd16) ? 5'd16 : y; // saturate
  endfunction
endpackage

// Checker for shifter
module shifter_sva (input logic clk, input logic [3:0] data_in, input logic select, input logic [4:0] data_out);
  import top_checks_pkg::*;
  default clocking cb @(posedge clk); endclocking

  // Exact functional check (including zero-extension)
  assert property (data_out == shift_ref(data_in, select))
    else $error("shifter: data_out mismatch. sel=%0b din=%0h dout=%0h", select, data_in, data_out);

  // Minimal coverage: hit both branches
  cover property (select == 1'b0);
  cover property (select == 1'b1);
endmodule

// Checker for next_power_of_two
module next_power_of_two_sva (input logic clk, input logic [4:0] data_in, input logic [4:0] data_out);
  import top_checks_pkg::*;
  default clocking cb @(posedge clk); endclocking

  // Output must be a single-hot (power-of-two) and non-zero
  assert property ($onehot(data_out))
    else $error("next_power_of_two: output not power-of-two. din=%0d dout=%0b", data_in, data_out);

  // Spec check (strictly larger power-of-two, saturating to 16) for non-zero inputs
  assert property ((data_in != 5'd0) |-> (data_out == next_pow2_strict(data_in)))
    else $error("next_power_of_two: spec mismatch. din=%0d dout=%0d exp=%0d",
                data_in, data_out, next_pow2_strict(data_in));

  // Coverage: hit each possible output bucket
  cover property (data_out == 5'd2);
  cover property (data_out == 5'd4);
  cover property (data_out == 5'd8);
  cover property (data_out == 5'd16);
endmodule

// End-to-end checker on top_module
module top_module_sva (input logic clk,
                       input logic [3:0] data,
                       input logic rotate,
                       input logic select,   // top has an unused input; we check its lack of effect
                       input logic [4:0] result);
  import top_checks_pkg::*;
  default clocking cb @(posedge clk); endclocking

  // End-to-end spec: result == next_pow2_strict(shift_ref(data, rotate))
  assert property (result == next_pow2_strict(shift_ref(data, rotate)))
    else $error("top: end-to-end mismatch. data=%0h rot=%0b res=%0d exp=%0d",
                data, rotate, result, next_pow2_strict(shift_ref(data, rotate)));

  // Prove 'select' has no effect on result (it's unused in DUT)
  assert property (($changed(select) && $stable({data, rotate})) |-> $stable(result))
    else $error("top: result incorrectly depends on 'select'");

  // Minimal branch coverage for rotate
  cover property (rotate == 1'b0);
  cover property (rotate == 1'b1);
endmodule

// Example bind statements (connect clk from your environment):
// bind shifter            shifter_sva           u_shifter_sva(.clk(tb_clk), .*);
// bind next_power_of_two  next_power_of_two_sva u_np2_sva     (.clk(tb_clk), .*);
// bind top_module         top_module_sva        u_top_sva     (.clk(tb_clk), .*);