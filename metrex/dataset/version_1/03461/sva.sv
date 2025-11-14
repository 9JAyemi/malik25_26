// SystemVerilog Assertions for regfile
// Bindable, concise, and focused on key behavior

module regfile_sva
(
  input  logic         clk,
  input  logic         nrst,
  input  logic         wr,
  input  logic [4:0]   raddr1, raddr2, waddr,
  input  logic [31:0]  din,
  input  logic [31:0]  dout1, dout2,
  input  logic [2:0]   R1,
  input  logic [7:0]   R2,

  // internal signals
  input  logic [31:0]  dout1_reg, dout2_reg,
  input  logic [2:0]   R1_reg,
  input  logic [7:0]   R2_reg,

  // DUT memory
  ref    logic [31:0]  mem [0:31]
);

  // Simple golden model to reference expected behavior
  logic [31:0] mem_m [0:31];
  logic [31:0] dout1_m, dout2_m;
  logic [2:0]  R1_m;
  logic [7:0]  R2_m;

  // Model mem write + async reset of mem[1]
  always_ff @(posedge clk or negedge nrst) begin
    if (!nrst) begin
      mem_m[5'd1] <= '0;
    end else begin
      if (wr) mem_m[waddr] <= din;
    end
  end

  // Model registered reads and taps
  always_ff @(posedge clk) begin
    dout1_m <= mem_m[raddr1];
    dout2_m <= mem_m[raddr2];
    R1_m    <= mem_m[5'd1][31:29];
    R2_m    <= mem_m[5'd2][7:0];
  end

  default clocking cb @(posedge clk); endclocking
  default disable iff (!nrst);

  // Async reset effect on mem[1]
  assert property (@(negedge nrst) mem[5'd1] == 32'h0);

  // Write updates memory at next clk
  assert property (wr |=> mem[$past(waddr)] == $past(din));

  // Connectivity/gating on read ports
  assert property (raddr1 == 5'd0 |-> dout1 == 32'h0);
  assert property (raddr2 == 5'd0 |-> dout2 == 32'h0);
  assert property (raddr1 != 5'd0 |-> dout1 == dout1_reg);
  assert property (raddr2 != 5'd0 |-> dout2 == dout2_reg);

  // Registered read timing matches model
  assert property (dout1_reg == dout1_m);
  assert property (dout2_reg == dout2_m);

  // Taps from mem[1] and mem[2]
  assert property (R1_reg == R1_m);
  assert property (R2_reg == R2_m);
  assert property (R1 == R1_reg);
  assert property (R2 == R2_reg);

  // Taps update correctly on writes to their backing locations
  assert property (wr && (waddr == 5'd1) |=> R1 == $past(din[31:29]));
  assert property (wr && (waddr == 5'd2) |=> R2 == $past(din[7:0]));

  // After reset deassert, R1 reflects reset mem[1]==0 on the first clock
  assert property ($rose(nrst) |-> R1 == 3'b000);

  // Functional covers
  cover property ($fell(nrst) ##[1:$] $rose(nrst));
  cover property (wr && (waddr == 5'd1) ##1 (R1 == $past(din[31:29])));
  cover property (wr && (waddr == 5'd2) ##1 (R2 == $past(din[7:0])));
  cover property (raddr1 == 5'd0 && dout1 == 32'h0);
  cover property (raddr2 == 5'd0 && dout2 == 32'h0);
  cover property (wr && (raddr1 == waddr)); // RW same-cycle hazard on port1
  cover property (wr && (raddr2 == waddr)); // RW same-cycle hazard on port2
  cover property (wr && (waddr != 5'd0) ##1 (raddr1 == $past(waddr)) && (dout1 == $past(din)));

endmodule

// Bind into the DUT
bind regfile regfile_sva i_regfile_sva (
  .clk(clk),
  .nrst(nrst),
  .wr(wr),
  .raddr1(raddr1),
  .raddr2(raddr2),
  .waddr(waddr),
  .din(din),
  .dout1(dout1),
  .dout2(dout2),
  .R1(R1),
  .R2(R2),
  .dout1_reg(dout1_reg),
  .dout2_reg(dout2_reg),
  .R1_reg(R1_reg),
  .R2_reg(R2_reg),
  .mem(mem)
);