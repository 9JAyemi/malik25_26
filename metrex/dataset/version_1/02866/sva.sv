// SVA checker for RegisterBanc
// - Minimal scoreboard to model architectural state
// - Asserts: data correctness, same-cycle write-read forwarding, ro consistency,
//            and X-propagation guards
// - Coverage: each reg written at least once, same-cycle hazards, ro write

module RegisterBanc_sva #(parameter int DW=32, AW=5, NREGS=(1<<AW)) (
  input  logic                 clk,
  input  logic                 RegWrite,
  input  logic [AW-1:0]        ReadAddr1,
  input  logic [AW-1:0]        ReadAddr2,
  input  logic [AW-1:0]        WriteAddr,
  input  logic [DW-1:0]        WriteData,
  input  logic [DW-1:0]        ReadData1,
  input  logic [DW-1:0]        ReadData2,
  input  logic [DW-1:0]        ro
);

  // Architectural reference model (no reset in DUT => init to 0)
  logic [DW-1:0] exp [NREGS];
  initial begin
    for (int i=0; i<NREGS; i++) exp[i] = '0;
  end
  always_ff @(posedge clk) begin
    if (RegWrite) exp[WriteAddr] <= WriteData;
  end

  // Avoid race with DUT updates
  clocking cb @(posedge clk);
    default input #1step;  // sample after NBA updates
    input RegWrite, ReadAddr1, ReadAddr2, WriteAddr, WriteData, ReadData1, ReadData2, ro;
  endclocking

  // X/Z guards on used controls/addresses/data
  ap_no_x_readaddr1: assert property (@cb !$isunknown(cb.ReadAddr1)) else $error("ReadAddr1 has X/Z");
  ap_no_x_readaddr2: assert property (@cb !$isunknown(cb.ReadAddr2)) else $error("ReadAddr2 has X/Z");
  ap_no_x_on_write:  assert property (@cb cb.RegWrite |-> !($isunknown(cb.WriteAddr) || $isunknown(cb.WriteData)))
                     else $error("WriteAddr/WriteData has X/Z when RegWrite=1");

  // Functional correctness: reads reflect architectural state
  ap_r1_correct: assert property (@cb cb.ReadData1 == exp[cb.ReadAddr1])
                 else $error("ReadData1 mismatch");
  ap_r2_correct: assert property (@cb cb.ReadData2 == exp[cb.ReadAddr2])
                 else $error("ReadData2 mismatch");
  ap_ro_correct: assert property (@cb cb.ro == exp[5'd2])
                 else $error("ro != Register[2] architectural value");

  // Same-cycle write-read forwarding (after the clock edge)
  ap_fwd_r1: assert property (@cb cb.RegWrite && (cb.ReadAddr1 == cb.WriteAddr) |-> (cb.ReadData1 == cb.WriteData))
             else $error("Forwarding failure on ReadData1");
  ap_fwd_r2: assert property (@cb cb.RegWrite && (cb.ReadAddr2 == cb.WriteAddr) |-> (cb.ReadData2 == cb.WriteData))
             else $error("Forwarding failure on ReadData2");
  ap_fwd_ro: assert property (@cb cb.RegWrite && (cb.WriteAddr == 5'd2) |-> (cb.ro == cb.WriteData))
             else $error("Forwarding failure on ro/Register[2]");

  // Optional: outputs should never be X/Z (given initialized storage)
  ap_no_x_r1: assert property (@cb !$isunknown(cb.ReadData1)) else $error("ReadData1 X/Z");
  ap_no_x_r2: assert property (@cb !$isunknown(cb.ReadData2)) else $error("ReadData2 X/Z");
  ap_no_x_ro: assert property (@cb !$isunknown(cb.ro))        else $error("ro X/Z");

  // Coverage
  genvar gi;
  generate
    for (gi=0; gi<NREGS; gi++) begin : gen_cov_wr_each
      cp_write_each: cover property (@cb cb.RegWrite && (cb.WriteAddr == gi));
    end
  endgenerate
  cp_samecycle_hazard_r1: cover property (@cb cb.RegWrite && (cb.ReadAddr1 == cb.WriteAddr));
  cp_samecycle_hazard_r2: cover property (@cb cb.RegWrite && (cb.ReadAddr2 == cb.WriteAddr));
  cp_write_ro:            cover property (@cb cb.RegWrite && (cb.WriteAddr == 5'd2));

endmodule

// Bind into the DUT
bind RegisterBanc RegisterBanc_sva #(.DW(32), .AW(5)) RegisterBanc_sva_i (
  .clk       (clk),
  .RegWrite  (RegWrite),
  .ReadAddr1 (ReadAddr1),
  .ReadAddr2 (ReadAddr2),
  .WriteAddr (WriteAddr),
  .WriteData (WriteData),
  .ReadData1 (ReadData1),
  .ReadData2 (ReadData2),
  .ro        (ro)
);