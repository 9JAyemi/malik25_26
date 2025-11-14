// SVA for vga_dac_regs
// Bind this file or place inside the module under an `ifdef

bind vga_dac_regs vga_dac_regs_sva sva_inst();

module vga_dac_regs_sva;
  // Access DUT scope directly via bind
  default clocking cb @(posedge clk); endclocking

  bit started;
  initial started = 1'b0;
  always @(posedge clk) started <= 1'b1;

  // Output datapath latency: outputs reflect previous cycle's RAM contents at previous index
  assert property (disable iff(!started) red   == $past(red_dac[index]));
  assert property (disable iff(!started) green == $past(green_dac[index]));
  assert property (disable iff(!started) blue  == $past(blue_dac[index]));

  // Read mux latency and default
  assert property (disable iff(!started) $past(read_data_cycle)==2'b00 |-> read_data == $past(red_dac[read_data_register]));
  assert property (disable iff(!started) $past(read_data_cycle)==2'b01 |-> read_data == $past(green_dac[read_data_register]));
  assert property (disable iff(!started) $past(read_data_cycle)==2'b10 |-> read_data == $past(blue_dac[read_data_register]));
  assert property (disable iff(!started) $past(read_data_cycle)==2'b11 |-> read_data == 4'h0);

  // Write behavior: correct target updated next cycle; others unchanged at that address
  property p_wr_red;
    logic [7:0] a; logic [3:0] d;
    disable iff(!started)
    (write && write_data_cycle==2'b00, a=write_data_register, d=write_data) |=>
      (red_dac[a] == d) &&
      (green_dac[a] == $past(green_dac[a])) &&
      (blue_dac[a]  == $past(blue_dac[a]));
  endproperty
  assert property (p_wr_red);

  property p_wr_green;
    logic [7:0] a; logic [3:0] d;
    disable iff(!started)
    (write && write_data_cycle==2'b01, a=write_data_register, d=write_data) |=>
      (green_dac[a] == d) &&
      (red_dac[a]   == $past(red_dac[a])) &&
      (blue_dac[a]  == $past(blue_dac[a]));
  endproperty
  assert property (p_wr_green);

  property p_wr_blue;
    logic [7:0] a; logic [3:0] d;
    disable iff(!started)
    (write && write_data_cycle==2'b10, a=write_data_register, d=write_data) |=>
      (blue_dac[a] == d) &&
      (red_dac[a]  == $past(red_dac[a])) &&
      (green_dac[a]== $past(green_dac[a]));
  endproperty
  assert property (p_wr_blue);

  // No-op write cycle (2'b11) must not modify any DAC at that address
  property p_wr_none;
    logic [7:0] a;
    disable iff(!started)
    (write && write_data_cycle==2'b11, a=write_data_register) |=>
      (red_dac[a]   == $past(red_dac[a])) &&
      (green_dac[a] == $past(green_dac[a])) &&
      (blue_dac[a]  == $past(blue_dac[a]));
  endproperty
  assert property (p_wr_none);

  // Basic no-X on visible outputs
  assert property (disable iff(!started) !$isunknown({red, green, blue, read_data}));

  // Coverage: exercise all write/read cycles
  cover property (write && write_data_cycle==2'b00);
  cover property (write && write_data_cycle==2'b01);
  cover property (write && write_data_cycle==2'b10);
  cover property (write && write_data_cycle==2'b11);

  cover property (read_data_cycle==2'b00);
  cover property (read_data_cycle==2'b01);
  cover property (read_data_cycle==2'b10);
  cover property (read_data_cycle==2'b11 |=> read_data==4'h0);

  // Coverage: write then read-back same address/channel -> returned data equals written data
  property p_wr_rd_back(input [1:0] cyc);
    logic [7:0] a; logic [3:0] d;
    (write && write_data_cycle==cyc, a=write_data_register, d=write_data)
      ##1 (read_data_cycle==cyc && read_data_register==a)
      ##1 (read_data==d);
  endproperty
  cover property (p_wr_rd_back(2'b00));
  cover property (p_wr_rd_back(2'b01));
  cover property (p_wr_rd_back(2'b10));
endmodule