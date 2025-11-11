// Bindable SVA checker for data_modifier
module data_modifier_sva #(parameter int W = 32) (
  input  logic                 clk,
  input  logic                 rst_n,
  input  logic [W-1:0]         reg_input,
  input  logic [3:0]           address,
  input  logic                 reg_out_syn,
  input  logic                 ack,
  input  logic                 ack_syn,
  input  logic [W-1:0]         reg_out
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Basic sanity (no X on controls/outputs)
  assert property ( !$isunknown({ack, ack_syn}) );
  assert property ( !$isunknown(reg_out_syn) );
  assert property ( !$isunknown(reg_out) );

  // Functional mapping (combinational, same-cycle)
  assert property ( (ack && !ack_syn) |-> ##0 reg_out == {reg_input[W-2:0], 1'b0} );
  assert property ( (!ack && ack_syn) |-> ##0 reg_out == {1'b0, reg_input[W-1:1]} );
  if (W == 32) begin
    assert property ( (ack && ack_syn) |-> ##0
                      reg_out == {reg_input[7:0], reg_input[15:8], reg_input[23:16], reg_input[31:24]} );
  end
  assert property ( (!ack && !ack_syn) |-> ##0 reg_out == reg_input );

  // reg_out_syn must reflect OR of acks
  assert property ( reg_out_syn == (ack || ack_syn) );

  // Stability guarantees
  assert property ( !$changed({reg_input, ack, ack_syn}) |-> ##0 $stable(reg_out) && $stable(reg_out_syn) );
  assert property ( $changed(address) && !$changed({reg_input, ack, ack_syn})
                    |-> ##0 $stable(reg_out) && $stable(reg_out_syn) );

  // Coverage: exercise each transform and strobe behavior
  cover property ( (ack && !ack_syn) ##0 reg_out == {reg_input[W-2:0], 1'b0} );
  cover property ( (!ack && ack_syn) ##0 reg_out == {1'b0, reg_input[W-1:1]} );
  if (W == 32) begin
    cover property ( (ack && ack_syn) ##0
                     reg_out == {reg_input[7:0], reg_input[15:8], reg_input[23:16], reg_input[31:24]} );
  end
  cover property ( (!ack && !ack_syn) ##0 reg_out == reg_input );
  cover property ( reg_out_syn == 1'b1 );
  cover property ( reg_out_syn == 1'b0 );
  cover property ( $changed(address) && !$changed({reg_input, ack, ack_syn}) );

endmodule

// Example bind (connect clk/rst_n from your TB/environment):
// bind data_modifier data_modifier_sva #(.W(32)) dm_chk (.* , .clk(tb_clk), .rst_n(tb_rst_n));