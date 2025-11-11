// SVA checker for soc_system_led_pio
module soc_system_led_pio_sva (
  input  logic        clk,
  input  logic        reset_n,
  input  logic        chipselect,
  input  logic        write_n,
  input  logic [1:0]  address,
  input  logic [31:0] writedata,
  input  logic [3:0]  out_port,
  input  logic [31:0] readdata
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset_n);

  // Write to address 0 updates out_port on next cycle
  assert property ( (chipselect && !write_n && address==2'd0 && $past(reset_n))
                    |=> out_port == $past(writedata[3:0]) );

  // No write to address 0 => out_port holds
  assert property ( !(chipselect && !write_n && address==2'd0) |=> $stable(out_port) );

  // Read datapath: when addr==0, low nibble mirrors out_port and upper bits are 0
  assert property ( (address==2'd0) |-> (readdata[31:4]==28'd0 && readdata[3:0]==out_port) );

  // Read datapath: when addr!=0, read returns 0
  assert property ( (address!=2'd0) |-> (readdata==32'd0) );

  // Upper bits of readdata are always zero
  assert property ( readdata[31:4]==28'd0 );

  // While in reset, output is the reset value
  assert property (@(posedge clk) !reset_n |-> (out_port==4'hF));

  // X-checks after reset deasserted
  assert property ( reset_n |-> (!$isunknown(out_port) && !$isunknown(readdata)) );

  // Coverage
  cover property ( $fell(reset_n) ); // reset assertion observed
  cover property ( $rose(reset_n) ); // reset release observed
  cover property ( chipselect && !write_n && address==2'd0 ); // a write to addr0
  cover property ( (chipselect && !write_n && address==2'd0)
                   ##1 (address==2'd0 && readdata[3:0]==out_port) ); // write then readback
  cover property ( (chipselect && !write_n && address==2'd0)
                   ##1 (chipselect && !write_n && address==2'd0) ); // back-to-back writes
  cover property ( address!=2'd0 && readdata==32'd0 ); // read from non-zero addr returns 0

endmodule

// Bind into DUT
bind soc_system_led_pio soc_system_led_pio_sva sva_i (
  .clk(clk),
  .reset_n(reset_n),
  .chipselect(chipselect),
  .write_n(write_n),
  .address(address),
  .writedata(writedata),
  .out_port(out_port),
  .readdata(readdata)
);