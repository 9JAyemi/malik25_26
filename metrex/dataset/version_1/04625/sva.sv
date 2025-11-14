// SVA for digital_design
module digital_design_sva (
  input logic clk,
  input logic rst,
  input logic enable,
  input logic test_expr,
  input logic prevConfigInvalid,
  input logic out
);

  default clocking @(posedge clk); endclocking

  logic past_valid;
  always_ff @(posedge clk) begin
    if (rst) past_valid <= 1'b0;
    else     past_valid <= 1'b1;
  end

  // Core behavior: synchronous reset clears, enable updates, else holds
  a_reset_clears: assert property (past_valid && $past(rst) |-> out == 1'b0);

  a_functional: assert property (disable iff (rst)
                                 past_valid |-> out ==
                                   ( $past(enable)
                                     ? ($past(test_expr) && !$past(prevConfigInvalid))
                                     : $past(out) ));

  // Sanity: no X on outputs after reset is released; inputs known when used
  a_out_known: assert property (disable iff (rst) !$isunknown(out));
  a_inputs_known_when_en: assert property (disable iff (rst)
                                           enable |-> (!$isunknown(test_expr) && !$isunknown(prevConfigInvalid)));

  // Coverage
  c_set1:          cover property (past_valid && $past(!rst && enable &&  test_expr && !prevConfigInvalid) && out == 1'b1);
  c_set0_expr0:    cover property (past_valid && $past(!rst && enable && !test_expr)                         && out == 1'b0);
  c_set0_invalid:  cover property (past_valid && $past(!rst && enable &&  prevConfigInvalid)                 && out == 1'b0);
  c_hold:          cover property (past_valid && $past(!rst && !enable)                                      && out == $past(out));
  c_reset:         cover property (past_valid && $past(rst)                                                  && out == 1'b0);

endmodule

bind digital_design digital_design_sva sva_i (
  .clk(clk),
  .rst(rst),
  .enable(enable),
  .test_expr(test_expr),
  .prevConfigInvalid(prevConfigInvalid),
  .out(out)
);