// SVA checker for barrel_shifter. Bind this to the DUT.
module barrel_shifter_sva
(
  input logic              clk,
  input logic [15:0]       in,
  input logic [3:0]        shift_amount,
  input logic [15:0]       out,
  input logic [15:0]       in_reg,
  input logic [3:0]        shift_amount_reg,
  input logic [15:0]       out_reg
);

  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  function automatic [15:0] rol16(input [15:0] d, input [3:0] s);
    rol16 = (d << s) | (d >> (16 - s));
  endfunction

  // Sanity: no X/Z on ports and key regs
  assert property (@(posedge clk) !$isunknown({in, shift_amount}));
  assert property (@(posedge clk) past_valid |-> !$isunknown({in_reg, shift_amount_reg}));
  assert property (@(posedge clk) !$isunknown(out));

  // Pipeline staging correctness
  assert property (@(posedge clk) past_valid |-> in_reg == $past(in));
  assert property (@(posedge clk) past_valid |-> shift_amount_reg == $past(shift_amount));

  // Functional correctness (external view, 1-cycle latency)
  assert property (@(posedge clk)
    past_valid && !$isunknown($past({in, shift_amount})) |-> out == rol16($past(in), $past(shift_amount))
  );

  // Internal compute consistency
  assert property (@(posedge clk)
    past_valid && !$isunknown($past({in_reg, shift_amount_reg})) |-> out_reg == rol16($past(in_reg), $past(shift_amount_reg))
  );

  // Out mirrors registered output
  assert property (@(posedge clk) out == out_reg);

  // Key corner cases
  assert property (@(posedge clk) past_valid && $past(shift_amount)==4'd0  |-> out == $past(in));
  assert property (@(posedge clk) past_valid && $past(shift_amount)==4'd8  |-> out == {$past(in)[7:0],  $past(in)[15:8]});
  assert property (@(posedge clk) past_valid && $past(shift_amount)==4'd15 |-> out == {$past(in)[0],    $past(in)[15:1]});

  // Coverage: hit all shift values; exercise wrap-around and identity
  genvar s;
  generate
    for (s=0; s<16; s++) begin : cov_shift_vals
      cover property (@(posedge clk) shift_amount == s[3:0]);
    end
  endgenerate

  cover property (@(posedge clk) past_valid && $past(shift_amount)==4'd1  && $past(in)==16'h8001 && out == rol16($past(in), 4'd1));
  cover property (@(posedge clk) past_valid && $past(shift_amount)==4'd0  && $past(in)==16'hFFFF && out == $past(in));

endmodule

// Bind to DUT (connects internal regs for stronger checks)
bind barrel_shifter barrel_shifter_sva u_barrel_shifter_sva(
  .clk(clk),
  .in(in),
  .shift_amount(shift_amount),
  .out(out),
  .in_reg(in_reg),
  .shift_amount_reg(shift_amount_reg),
  .out_reg(out_reg)
);