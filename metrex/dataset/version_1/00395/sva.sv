// SVA for Distributed_RAM
// Bindable, concise, and checks key behavior with a shadow model.

module Distributed_RAM_sva #(
  parameter AddressWidth = 8,
  parameter DataWidth    = 8,
  parameter Depth        = 256
)(
  input  logic                      Clock_in,
  input  logic                      Write_Enable_in,
  input  logic [AddressWidth-1:0]   Address_in,
  input  logic [DataWidth-1:0]      Data_in,
  input  logic [DataWidth-1:0]      Data_out
);

  // Simple shadow model
  logic [DataWidth-1:0] ref_mem [Depth];

  initial begin
    for (int i=0;i<Depth;i++) ref_mem[i] = '0;
  end

  // Update ref model on writes
  always_ff @(posedge Clock_in) begin
    if (Write_Enable_in && !$isunknown({Address_in,Data_in}) && (Address_in < Depth))
      ref_mem[Address_in] <= Data_in;
  end

  default clocking cb @(posedge Clock_in); endclocking

  // Sanity/X checks
  a_ctrl_known:  assert property ( !$isunknown(Write_Enable_in) );
  a_addr_known:  assert property ( !$isunknown(Address_in) );
  a_din_when_we: assert property ( Write_Enable_in |-> !$isunknown(Data_in) );
  a_addr_range:  assert property ( !$isunknown(Address_in) |-> (Address_in < Depth) );

  // Functional: Data_out equals shadow model (sample after NBA)
  a_dout_matches_model: assert property (
    ( !$isunknown(Address_in) && (Address_in < Depth) ) |-> ##0 (Data_out == ref_mem[Address_in])
  );

  // Same-cycle write-through when writing the addressed location
  a_write_through: assert property (
    ( Write_Enable_in && !$isunknown({Address_in,Data_in}) && (Address_in < Depth) ) |-> ##0 (Data_out == Data_in)
  );

  // No-write + same address => value holds across cycles
  a_hold_when_no_we: assert property (
    ( !Write_Enable_in && $stable(Address_in) && !$isunknown(Address_in) && (Address_in < Depth) )
      |-> ##1 (Data_out == $past(Data_out))
  );

  // Data_out not X on valid address
  a_dout_known_on_valid_addr: assert property (
    ( !$isunknown(Address_in) && (Address_in < Depth) ) |-> ##0 !$isunknown(Data_out)
  );

  // Coverage
  c_any_write:              cover property ( Write_Enable_in );
  c_b2b_writes:             cover property ( Write_Enable_in [*2] );
  c_write_addr_lo:          cover property ( Write_Enable_in && (Address_in == '0) );
  c_write_addr_hi:          cover property ( Write_Enable_in && (Address_in == Depth-1) );
  c_write_through_observed: cover property ( Write_Enable_in && (Address_in < Depth) ##0 (Data_out == Data_in) );
  c_writes_diff_addr:       cover property ( Write_Enable_in ##1 (Write_Enable_in && (Address_in != $past(Address_in))) );

endmodule

// Example bind (parameters follow the DUT instance's parameters)
bind Distributed_RAM Distributed_RAM_sva #(
  .AddressWidth(AddressWidth),
  .DataWidth(DataWidth),
  .Depth(Depth)
) u_Distributed_RAM_sva (
  .Clock_in(Clock_in),
  .Write_Enable_in(Write_Enable_in),
  .Address_in(Address_in),
  .Data_in(Data_in),
  .Data_out(Data_out)
);