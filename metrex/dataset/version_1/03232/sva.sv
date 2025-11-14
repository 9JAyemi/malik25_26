// SVA for serial_wb_parport
// Bindable checker; references internal regs via bind
module serial_wb_parport_sva
(
  input logic         clk_i,
  input logic         rst_i,
  input logic [31:0]  parport_i,
  input logic         writestrobe_i,
  input logic [7:0]   data_i,
  input logic [1:0]   address_i,
  input logic         readstrobe_i,
  input logic [31:0]  parport_o,
  input logic [7:0]   data_o,
  input logic         parport_writestrobe_o,
  input logic         parport_readstrobe_o,
  input logic [23:0]  outputreg_r,
  input logic [23:0]  inputreg_r
);

  default clocking cb @(posedge clk_i); endclocking
  default disable iff (rst_i);

  // Basic protocol sanity
  // Writes and reads should not be asserted together (flag if they are)
  assert property ( !(writestrobe_i && readstrobe_i) );

  // Combinational outputs
  assert property ( parport_readstrobe_o == (readstrobe_i && (address_i==2'b00)) );

  // data_o muxing (guard against X in inputreg_r)
  assert property ( (address_i==2'b00) |-> (data_o === parport_i[7:0]) );
  assert property ( (address_i inside {2'b01,2'b10,2'b11}) && !$isunknown(inputreg_r)
                    |-> (data_o === (address_i==2'b01 ? inputreg_r[7:0] :
                                     address_i==2'b10 ? inputreg_r[15:8] :
                                                        inputreg_r[23:16])) );

  // Reset effects (synchronous)
  assert property ( $rose(rst_i) |=> (parport_o==32'h0 && outputreg_r==24'h0 && !parport_writestrobe_o) );

  // Write strobe behavior
  assert property ( parport_writestrobe_o == (writestrobe_i && address_i==2'b11) );
  assert property ( parport_writestrobe_o |=> !parport_writestrobe_o ); // 1-cycle pulse

  // outputreg_r byte writes and holding of other bytes
  assert property ( (writestrobe_i && address_i==2'b00)
                    |=> (outputreg_r[7:0]  == $past(data_i) &&
                         outputreg_r[23:8] == $past(outputreg_r[23:8]) &&
                         parport_o == $past(parport_o)) );
  assert property ( (writestrobe_i && address_i==2'b01)
                    |=> (outputreg_r[15:8] == $past(data_i) &&
                         {outputreg_r[23:16],outputreg_r[7:0]} == $past({outputreg_r[23:16],outputreg_r[7:0]}) &&
                         parport_o == $past(parport_o)) );
  assert property ( (writestrobe_i && address_i==2'b10)
                    |=> (outputreg_r[23:16] == $past(data_i) &&
                         outputreg_r[15:0]   == $past(outputreg_r[15:0]) &&
                         parport_o == $past(parport_o)) );

  // Commit write (address 11): parport_o update and outputreg_r stability
  assert property ( (writestrobe_i && address_i==2'b11)
                    |=> (parport_o == {$past(data_i), $past(outputreg_r)} && $stable(outputreg_r)) );

  // parport_o only changes on commit write or reset
  assert property ( !(writestrobe_i && address_i==2'b11) |=> $stable(parport_o) );

  // Read side capture into inputreg_r only when readstrobe_i && addr==00 and no concurrent write (due to else-if)
  assert property ( (readstrobe_i && address_i==2'b00 && !writestrobe_i)
                    |=> (inputreg_r == $past(parport_i[31:8])) );
  // Otherwise inputreg_r holds
  assert property ( !(readstrobe_i && address_i==2'b00 && !writestrobe_i) |=> $stable(inputreg_r) );

  // If readstrobe_o asserted and no write, capture must occur
  assert property ( (parport_readstrobe_o && !writestrobe_i)
                    |=> (inputreg_r == $past(parport_i[31:8])) );

  // Coverage
  cover property ( (writestrobe_i && address_i==2'b00)
                   ##1 (writestrobe_i && address_i==2'b01)
                   ##1 (writestrobe_i && address_i==2'b10)
                   ##1 (writestrobe_i && address_i==2'b11 && parport_writestrobe_o) );

  cover property ( (readstrobe_i && address_i==2'b00)
                   ##1 (readstrobe_i && address_i==2'b01)
                   ##1 (readstrobe_i && address_i==2'b10)
                   ##1 (readstrobe_i && address_i==2'b11) );

endmodule

bind serial_wb_parport serial_wb_parport_sva sva (.*);