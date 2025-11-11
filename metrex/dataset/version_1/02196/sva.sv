// SVA for r_FAULT_STATUS
// Concise, high-quality checks with essential coverage

module r_FAULT_STATUS_sva (
  input logic         clk,
  input logic         reset,    // synchronous, active-high
  input logic         wenb,     // active-low write enable
  input logic [7:0]   in_data,
  input logic [7:0]   reg_0x1F
);
  default clocking cb @(posedge clk); endclocking

  // Control integrity
  a_ctrl_known: assert property (!$isunknown({reset, wenb}))
    else $error("X/Z on control signals");

  // Write data must be known when writing
  a_data_known_on_write: assert property (wenb==1'b1 or !$isunknown(in_data))
    else $error("in_data X/Z when write enabled (wenb==0)");

  // Reset clears next cycle (synchronous)
  a_reset_clears: assert property (reset |=> reg_0x1F == 8'h00)
    else $error("Reset did not clear reg_0x1F");

  // While reset is asserted, register remains zero
  a_reset_holds_zero: assert property ($past(reset) |-> reg_0x1F == 8'h00)
    else $error("reg_0x1F not 0 while reset held");

  // Active-low write updates next cycle
  a_write_updates: assert property (!reset && (wenb==1'b0) |=> reg_0x1F == $past(in_data))
    else $error("Write did not update reg_0x1F to in_data");

  // When not writing, value holds
  a_hold_when_no_write: assert property (!reset && (wenb==1'b1) |=> reg_0x1F == $past(reg_0x1F))
    else $error("reg_0x1F changed without write");

  // Any change must have a cause (reset or write)
  a_change_has_cause: assert property (reg_0x1F != $past(reg_0x1F) |-> $past(reset) || $past(!reset && wenb==1'b0))
    else $error("reg_0x1F changed without reset or write");

  // Coverage
  c_reset_event:       cover property (reset);
  c_write_event:       cover property (!reset && (wenb==1'b0) ##1 reg_0x1F == $past(in_data));
  c_hold_event:        cover property (!reset && (wenb==1'b1) ##1 reg_0x1F == $past(reg_0x1F));
  c_reset_then_write:  cover property (reset ##1 !reset && wenb==1'b0);
  c_write_00:          cover property (!reset && wenb==1'b0 && in_data==8'h00);
  c_write_FF:          cover property (!reset && wenb==1'b0 && in_data==8'hFF);
endmodule

// Bind into DUT
bind r_FAULT_STATUS r_FAULT_STATUS_sva sva_i (
  .clk(clk),
  .reset(reset),
  .wenb(wenb),
  .in_data(in_data),
  .reg_0x1F(reg_0x1F)
);