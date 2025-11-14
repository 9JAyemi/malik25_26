// SVA for up_down_counter
module up_down_counter_sva #(parameter WIDTH=8, LOADW=4)
(
  input logic                clk,
  input logic                up_down,
  input logic [LOADW-1:0]    load,
  input logic [WIDTH-1:0]    count
);

  default clocking @(posedge clk); endclocking

  // past-valid guard
  logic past_valid; initial past_valid = 0;
  always @(posedge clk) past_valid <= 1;

  // X/Z checks (skip first sampled cycle)
  a_inputs_known:  assert property (past_valid |-> !$isunknown({up_down, load}));
  a_count_known:   assert property (past_valid |-> !$isunknown(count));

  // Load has priority and zero-extends into count
  a_load_zeroext:  assert property (past_valid && (load != '0) |=> count == {{(WIDTH-LOADW){1'b0}}, $past(load)});

  // Increment when load==0 and up_down==1
  a_inc:           assert property (past_valid && (load == '0) && up_down |=> count == $past(count) + 1'b1);

  // Decrement when load==0 and up_down==0
  a_dec:           assert property (past_valid && (load == '0) && !up_down |=> count == $past(count) - 1'b1);

  // Basic functional coverage
  c_load:          cover  property (past_valid && (load != '0) |=> count == {{(WIDTH-LOADW){1'b0}}, $past(load)});
  c_inc:           cover  property (past_valid && (load == '0) && up_down |=> count == $past(count) + 1'b1);
  c_dec:           cover  property (past_valid && (load == '0) && !up_down |=> count == $past(count) - 1'b1);

  // Wrap-around coverage
  c_inc_wrap:      cover  property (past_valid && $past(load) == '0 && $past(up_down) && $past(count) == {WIDTH{1'b1}} ##1 count == '0);
  c_dec_wrap:      cover  property (past_valid && $past(load) == '0 && !$past(up_down) && $past(count) == '0 ##1 count == {WIDTH{1'b1}});

  // Branch coverage sequence: load -> inc -> dec
  c_branch_seq:    cover  property ((load != '0) ##1 ((load == '0) && up_down) ##1 ((load == '0) && !up_down));

endmodule

// Bind into DUT
bind up_down_counter up_down_counter_sva #(.WIDTH(8), .LOADW(4))
  up_down_counter_sva_i (.clk(clk), .up_down(up_down), .load(load), .count(count));