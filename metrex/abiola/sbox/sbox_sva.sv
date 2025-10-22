`timescale 1ns/1ps

module sbox_sva();

  // signals for interfacing with DUT
  logic clk;
  logic reset;
  logic [7:0] data_i;
  logic decrypt_i;
  logic [7:0] data_o;

  // Instantiate DUT
  sbox dut (
    .clk(clk),
    .reset(reset),
    .data_i(data_i),
    .decrypt_i(decrypt_i),
    .data_o(data_o)
  );

  // simple clock
  initial clk = 0;
  always #5 clk = ~clk;

  // Reset check (active low): after reset is asserted, some internal regs are zero
  // Use $past to observe next-cycle behavior
  property p_reset_clears_regs;
    @(posedge clk) disable iff (0) !$past(reset) |-> (dut.to_invert == 4'b0000 && dut.ah_reg == 4'b0000 && dut.alph == 4'b0000);
  endproperty
  assert property (p_reset_clears_regs) else $error("Reset did not clear internal registers as expected");

  // Pipeline update property: on posedge clk the registers follow the next_* combinational signals
  property p_pipeline_update;
    @(posedge clk) disable iff (0) $rose(clk) |-> (dut.to_invert == $past(dut.next_to_invert) && dut.ah_reg == $past(dut.next_ah_reg) && dut.alph == $past(dut.next_alph));
  endproperty
  assert property (p_pipeline_update) else $error("Pipeline registers didn't update from next_* signals on clock edge");

  // Combinational relation: next_alph == al ^ ah
  always @(*) begin
    assert (dut.next_alph == (dut.al ^ dut.ah)) else $error("next_alph is not al ^ ah: al=%b ah=%b next_alph=%b", dut.al, dut.ah, dut.next_alph);
  end

  // When decrypt_i is 1 (decrypt path), final output should match inva through end_mux logic
  // Here we assert data_o == inva when decrypt_i != 0 (RTL's end_mux sets data_o=inva under default/decrypt mapping)
  always @(posedge clk) begin
    if (decrypt_i)
      assert (data_o == dut.inva) else $error("decrypt_i set but data_o != inva: data_o=%b inva=%b", data_o, dut.inva);
  end

  // Stability: data_o should not toggle inside the clock half-cycle
  logic [7:0] data_o_pos;
  always @(posedge clk) data_o_pos <= data_o;
  always @(negedge clk) begin
    assert (data_o == data_o_pos) else $error("data_o changed mid-cycle: posedge=%b negedge=%b", data_o_pos, data_o);
  end

  // small stimulus to exercise simulation assertions
  initial begin
    reset = 0; data_i = 8'h00; decrypt_i = 0; #20;
    reset = 1; #20;
    data_i = 8'h3C; decrypt_i = 0; #20;
    data_i = 8'hA5; decrypt_i = 1; #40;
    $finish;
  end

endmodule
