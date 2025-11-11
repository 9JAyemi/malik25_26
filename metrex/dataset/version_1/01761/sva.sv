// SVA for soc_system_pio_led
module soc_system_pio_led_sva (
  input  logic        clk,
  input  logic        reset_n,
  input  logic        chipselect,
  input  logic        write_n,
  input  logic [1:0]  address,
  input  logic [31:0] writedata,
  input  logic [7:0]  data_out,   // internal reg bound hierarchically
  input  logic [7:0]  out_port,
  input  logic [31:0] readdata
);
  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset value must hold whenever reset is asserted
  assert property (!reset_n |-> data_out == 8'hFF);

  // Write to address 0 updates data_out with writedata[7:0] on next clock
  assert property (disable iff (!reset_n)
                   (chipselect && !write_n && address==2'b00)
                   |=> data_out == $past(writedata[7:0]));

  // No unintended update: if no write to addr 0, data_out holds its value
  assert property (disable iff (!reset_n)
                   !(chipselect && !write_n && address==2'b00)
                   |=> data_out == $past(data_out));

  // out_port always mirrors data_out
  assert property (out_port == data_out);

  // readdata mapping: addr==0 -> zero-extended data_out; else all zeros
  assert property ((address==2'b00) |-> (readdata[7:0] == data_out
                                      && readdata[31:8] == 24'h0));
  assert property ((address!=2'b00) |-> (readdata == 32'h0));

  // No X/Z on key outputs when out of reset
  assert property (disable iff (!reset_n) !$isunknown({out_port, readdata, data_out}));

  // Coverage
  cover property (!reset_n ##1 reset_n); // reset assert/deassert observed
  cover property (disable iff (!reset_n)
                  (chipselect && !write_n && address==2'b00)
                  ##1 (data_out == $past(writedata[7:0]))); // a valid write occurs
  cover property ((address==2'b00) && (readdata[7:0]==data_out)); // readback window
  cover property ((address!=2'b00) && (readdata==32'h0)); // zero when not addr 0
endmodule

// Bind into DUT (bind internal data_out explicitly)
bind soc_system_pio_led soc_system_pio_led_sva sva (
  .clk(clk),
  .reset_n(reset_n),
  .chipselect(chipselect),
  .write_n(write_n),
  .address(address),
  .writedata(writedata),
  .data_out(data_out),
  .out_port(out_port),
  .readdata(readdata)
);