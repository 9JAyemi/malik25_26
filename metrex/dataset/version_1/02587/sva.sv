// SVA for RAM_DUAL_READ_PORT and RAM_SINGLE_READ_PORT
// Concise, high-quality checks with lightweight reference model and key coverage

`ifndef RAM_SVA_ONCE
`define RAM_SVA_ONCE

// ---------------- Dual-read-port RAM ----------------
module RAM_DUAL_READ_PORT_sva #(
  parameter DATA_WIDTH=16,
  parameter ADDR_WIDTH=8,
  parameter MEM_SIZE=8
)(
  input  logic                      Clock,
  input  logic                      iWriteEnable,
  input  logic [ADDR_WIDTH-1:0]     iReadAddress0,
  input  logic [ADDR_WIDTH-1:0]     iReadAddress1,
  input  logic [ADDR_WIDTH-1:0]     iWriteAddress,
  input  logic [DATA_WIDTH-1:0]     iDataIn,
  input  logic [DATA_WIDTH-1:0]     oDataOut0,
  input  logic [DATA_WIDTH-1:0]     oDataOut1
);
  // simple golden model and validity mask (no reset -> learn-by-write)
  logic [DATA_WIDTH-1:0] model [MEM_SIZE:0];
  logic [MEM_SIZE:0]     valid;
  logic [ADDR_WIDTH-1:0] ra0_q, ra1_q;
  bit initdone;

  always_ff @(posedge Clock) begin
    initdone <= 1'b1;
    ra0_q <= iReadAddress0;
    ra1_q <= iReadAddress1;
    if (iWriteEnable && (iWriteAddress <= MEM_SIZE)) begin
      model[iWriteAddress] <= iDataIn;
      valid[iWriteAddress] <= 1'b1;
    end
  end

  // Address range checks
  assert property (@(posedge Clock) iReadAddress0 <= MEM_SIZE)
    else $error("iReadAddress0 out of range");
  assert property (@(posedge Clock) iReadAddress1 <= MEM_SIZE)
    else $error("iReadAddress1 out of range");
  assert property (@(posedge Clock) !iWriteEnable || (iWriteAddress <= MEM_SIZE))
    else $error("iWriteAddress out of range when writing");

  // Functional: 1-cycle registered, read-before-write semantics
  assert property (@(posedge Clock)
                   initdone && (ra0_q <= MEM_SIZE) && valid[ra0_q]
                   |-> ##0 (oDataOut0 == model[ra0_q]))
    else $error("Port0 data mismatch vs model (1-cycle latency)");
  assert property (@(posedge Clock)
                   initdone && (ra1_q <= MEM_SIZE) && valid[ra1_q]
                   |-> ##0 (oDataOut1 == model[ra1_q]))
    else $error("Port1 data mismatch vs model (1-cycle latency)");

  // Coherency: same address on both read ports -> same data
  assert property (@(posedge Clock)
                   (iReadAddress0 == iReadAddress1) && (iReadAddress0 <= MEM_SIZE)
                   |-> ##0 (oDataOut0 == oDataOut1))
    else $error("Dual-read coherency mismatch");

  // Outputs must be known once address content is known
  assert property (@(posedge Clock)
                   valid[ra0_q] && (ra0_q <= MEM_SIZE)
                   |-> ##0 !$isunknown(oDataOut0))
    else $error("oDataOut0 unknown on known address");
  assert property (@(posedge Clock)
                   valid[ra1_q] && (ra1_q <= MEM_SIZE)
                   |-> ##0 !$isunknown(oDataOut1))
    else $error("oDataOut1 unknown on known address");

  // Coverage: key interactions and extremes
  cover property (@(posedge Clock) iWriteEnable && (iWriteAddress == '0));
  cover property (@(posedge Clock) iWriteEnable && (iWriteAddress == MEM_SIZE));
  cover property (@(posedge Clock) iWriteEnable && (iWriteAddress == iReadAddress0));
  cover property (@(posedge Clock) iWriteEnable && (iWriteAddress == iReadAddress1));
  cover property (@(posedge Clock) (iReadAddress0 == iReadAddress1));
  cover property (@(posedge Clock) initdone && iWriteEnable ##1 (iReadAddress0 == $past(iWriteAddress)));
  cover property (@(posedge Clock) initdone && iWriteEnable ##1 (iReadAddress1 == $past(iWriteAddress)));
endmodule

bind RAM_DUAL_READ_PORT RAM_DUAL_READ_PORT_sva #(
  .DATA_WIDTH(DATA_WIDTH), .ADDR_WIDTH(ADDR_WIDTH), .MEM_SIZE(MEM_SIZE)
) RAM_DUAL_READ_PORT_sva_b (.*);

// ---------------- Single-read-port RAM ----------------
module RAM_SINGLE_READ_PORT_sva #(
  parameter DATA_WIDTH=16,
  parameter ADDR_WIDTH=8,
  parameter MEM_SIZE=8
)(
  input  logic                      Clock,
  input  logic                      iWriteEnable,
  input  logic [ADDR_WIDTH-1:0]     iReadAddress,
  input  logic [ADDR_WIDTH-1:0]     iWriteAddress,
  input  logic [DATA_WIDTH-1:0]     iDataIn,
  input  logic [DATA_WIDTH-1:0]     oDataOut
);
  logic [DATA_WIDTH-1:0] model [MEM_SIZE:0];
  logic [MEM_SIZE:0]     valid;
  logic [ADDR_WIDTH-1:0] ra_q;
  bit initdone;

  always_ff @(posedge Clock) begin
    initdone <= 1'b1;
    ra_q <= iReadAddress;
    if (iWriteEnable && (iWriteAddress <= MEM_SIZE)) begin
      model[iWriteAddress] <= iDataIn;
      valid[iWriteAddress] <= 1'b1;
    end
  end

  assert property (@(posedge Clock) iReadAddress <= MEM_SIZE)
    else $error("iReadAddress out of range");
  assert property (@(posedge Clock) !iWriteEnable || (iWriteAddress <= MEM_SIZE))
    else $error("iWriteAddress out of range when writing");

  assert property (@(posedge Clock)
                   initdone && (ra_q <= MEM_SIZE) && valid[ra_q]
                   |-> ##0 (oDataOut == model[ra_q]))
    else $error("Data mismatch vs model (1-cycle latency)");

  assert property (@(posedge Clock)
                   valid[ra_q] && (ra_q <= MEM_SIZE)
                   |-> ##0 !$isunknown(oDataOut))
    else $error("oDataOut unknown on known address");

  // Coverage
  cover property (@(posedge Clock) iWriteEnable && (iWriteAddress == '0));
  cover property (@(posedge Clock) iWriteEnable && (iWriteAddress == MEM_SIZE));
  cover property (@(posedge Clock) iWriteEnable && (iWriteAddress == iReadAddress));
  cover property (@(posedge Clock) initdone && iWriteEnable ##1 (iReadAddress == $past(iWriteAddress)));
endmodule

bind RAM_SINGLE_READ_PORT RAM_SINGLE_READ_PORT_sva #(
  .DATA_WIDTH(DATA_WIDTH), .ADDR_WIDTH(ADDR_WIDTH), .MEM_SIZE(MEM_SIZE)
) RAM_SINGLE_READ_PORT_sva_b (.*);

`endif