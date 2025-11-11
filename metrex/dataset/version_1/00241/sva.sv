// SVA for the given design. Focused, high-quality checks with concise coverage.

module barrel_shifter_sva #(parameter W=16, AW=5) (
  input logic                clk,
  input logic                reset,
  input logic [W-1:0]        data_in,
  input logic [AW-1:0]       shift_amt,
  input logic                left_enable,
  input logic                right_enable,
  input logic [W-1:0]        data_out
);
  default clocking cb @(posedge clk); endclocking

  // Correctness and priority
  assert property (reset |=> data_out == '0);
  assert property (!reset &&  left_enable && !right_enable |=> data_out == (data_in << shift_amt));
  assert property (!reset && !left_enable &&  right_enable |=> data_out == (data_in >> shift_amt));
  assert property (!reset && !left_enable && !right_enable |=> data_out == data_in);
  // If both enables high, left has priority (as coded)
  assert property (!reset && left_enable && right_enable |=> data_out == (data_in << shift_amt));

  // Knownness
  assert property (!$isunknown(data_out));

  // Coverage (branches and edge shift amounts)
  cover property (!reset && left_enable);
  cover property (!reset && right_enable);
  cover property (!reset && left_enable  && shift_amt == '0);
  cover property (!reset && right_enable && shift_amt == '0);
  cover property (!reset && left_enable  && shift_amt == (W-1));
  cover property (!reset && right_enable && shift_amt == (W-1));
  cover property (!reset && (left_enable || right_enable) && shift_amt >= W);
endmodule


module top_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [15:0] data,
  input  logic [4:0]  shift_amt,
  input  logic [1:0]  select,
  input  logic [7:0]  q,
  // internal wires from top_module
  input  logic [15:0] shifted_data,
  input  logic [7:0]  lower_nibble,
  input  logic [7:0]  upper_nibble,
  input  logic [7:0]  xor_output
);
  default clocking cb @(posedge clk); endclocking

  function automatic logic [15:0] exp_shift (
    logic rst, logic [15:0] din, logic [4:0] amt, logic [1:0] sel
  );
    if (rst)                exp_shift = 16'h0000;
    else if (sel == 2'b01)  exp_shift = din << amt;
    else if (sel == 2'b10)  exp_shift = din >> amt;
    else                    exp_shift = din;
  endfunction

  let ES = exp_shift($past(reset), $past(data), $past(shift_amt), $past(select));

  // Internal datapath checks (1-cycle delayed to avoid race with NBA/comb settle)
  assert property (1 |=> (lower_nibble == shifted_data[7:0]) && (upper_nibble == shifted_data[15:8]));
  assert property (1 |=> xor_output == (lower_nibble ^ upper_nibble));
  assert property (1 |=> ((select == 2'b00) ? (q == xor_output)
                          : (select == 2'b01) ? (q == lower_nibble)
                                              : (q == upper_nibble)));

  // End-to-end functional check from inputs to q (accounts for register latency)
  assert property (1 |=> q == ((select == 2'b00) ? (ES[7:0] ^ ES[15:8])
                              : (select == 2'b01) ?  ES[7:0]
                                                  :  ES[15:8]));

  // Reset drives q low on next cycle
  assert property (reset |=> q == 8'h00);

  // Knownness
  assert property (!$isunknown({shifted_data, lower_nibble, upper_nibble, xor_output, q}));

  // Coverage: select branches and edge shift amounts in each shift direction
  cover property (!reset && select == 2'b00);
  cover property (!reset && select == 2'b01);
  cover property (!reset && select == 2'b10);
  cover property (!reset && select == 2'b11);

  cover property (!reset ##1 (select == 2'b01 && shift_amt == 0));
  cover property (!reset ##1 (select == 2'b01 && shift_amt == 15));
  cover property (!reset ##1 (select == 2'b01 && shift_amt >= 16));

  cover property (!reset ##1 (select == 2'b10 && shift_amt == 0));
  cover property (!reset ##1 (select == 2'b10 && shift_amt == 15));
  cover property (!reset ##1 (select == 2'b10 && shift_amt >= 16));
endmodule


// Bind assertions to DUT
bind barrel_shifter barrel_shifter_sva #(.W(16), .AW(5)) bs_sva (
  .clk(clk),
  .reset(reset),
  .data_in(data_in),
  .shift_amt(shift_amt),
  .left_enable(left_enable),
  .right_enable(right_enable),
  .data_out(data_out)
);

bind top_module top_module_sva tm_sva (
  .clk(clk),
  .reset(reset),
  .data(data),
  .shift_amt(shift_amt),
  .select(select),
  .q(q),
  .shifted_data(shifted_data),
  .lower_nibble(lower_nibble),
  .upper_nibble(upper_nibble),
  .xor_output(xor_output)
);