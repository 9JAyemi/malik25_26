// SVA checker for RegisterFile. Bind this to the DUT.
module RegisterFile_sva (
  input        clk,
  input        wr_en,
  input  [2:0] wr_addr,
  input  [7:0] wr_data,
  input  [2:0] rd1_addr,
  input  [2:0] rd2_addr,
  input  [7:0] rd1_data,
  input  [7:0] rd2_data
);

  default clocking cb @ (posedge clk); endclocking
  bit started; always_ff @(posedge clk) started <= 1'b1;

  // Simple golden model (state after previous cycle)
  logic [7:0] model [0:7];
  bit         model_v [0:7]; // valid flags per address
  initial model_v = '{default:0};

  // Update model on known writes
  always_ff @(posedge clk) begin
    if (wr_en===1'b1 && !$isunknown({wr_addr,wr_data})) begin
      model[wr_addr]   <= wr_data;
      model_v[wr_addr] <= 1'b1;
    end
  end

  // Core correctness: next-cycle read data matches model at current address
  assert property (disable iff(!started)
    (!$isunknown(rd1_addr) && model_v[rd1_addr]) |=> (rd1_data == model[rd1_addr]))
    else $error("rd1_data mismatch vs model at addr %0d", rd1_addr);

  assert property (disable iff(!started)
    (!$isunknown(rd2_addr) && model_v[rd2_addr]) |=> (rd2_data == model[rd2_addr]))
    else $error("rd2_data mismatch vs model at addr %0d", rd2_addr);

  // If both ports address the same entry, next-cycle data must match on both ports
  assert property (disable iff(!started)
    (!$isunknown(rd1_addr) && rd1_addr==rd2_addr && model_v[rd1_addr]) |=> (rd1_data==rd2_data))
    else $error("Dual-read mismatch at addr %0d", rd1_addr);

  // X-protection on controls and addresses
  assert property (disable iff(!started) wr_en !== 1'bx)
    else $error("wr_en is X");
  assert property (disable iff(!started) !$isunknown(rd1_addr))
    else $error("rd1_addr is X");
  assert property (disable iff(!started) !$isunknown(rd2_addr))
    else $error("rd2_addr is X");
  assert property (disable iff(!started) (wr_en===1'b0) or (wr_en===1'b1 && !$isunknown({wr_addr,wr_data})))
    else $error("wr_addr/wr_data unknown when wr_en=1");

  // Read-after-write visibility on next cycle (both ports)
  assert property (disable iff(!started)
    (wr_en===1'b1 && !$isunknown({wr_addr,wr_data})) ##1 (rd1_addr==$past(wr_addr)) |-> (rd1_data==$past(wr_data)))
    else $error("Port1 failed RAW next-cycle visibility");
  assert property (disable iff(!started)
    (wr_en===1'b1 && !$isunknown({wr_addr,wr_data})) ##1 (rd2_addr==$past(wr_addr)) |-> (rd2_data==$past(wr_data)))
    else $error("Port2 failed RAW next-cycle visibility");

  // Coverage
  cover property (disable iff(!started)
    wr_en===1'b1 && !$isunknown({wr_addr,wr_data})); // any clean write

  cover property (disable iff(!started)
    (wr_en===1'b1 && !$isunknown({wr_addr,wr_data})) ##1 (rd1_addr==$past(wr_addr)) && (rd1_data==$past(wr_data))); // write->read on port1

  cover property (disable iff(!started)
    (wr_en===1'b1 && !$isunknown({wr_addr,wr_data})) ##1 (rd2_addr==$past(wr_addr)) && (rd2_data==$past(wr_data))); // write->read on port2

  cover property (disable iff(!started)
    (rd1_addr==rd2_addr) ##1 (rd1_data==rd2_data)); // both ports same addr -> same data

  cover property (disable iff(!started)
    wr_en===1'b1 && wr_addr==3'd0);
  cover property (disable iff(!started)
    wr_en===1'b1 && wr_addr==3'd7);

  cover property (disable iff(!started)
    wr_en===1'b1 && rd1_addr==wr_addr); // same-cycle RAW hazard seen on port1
  cover property (disable iff(!started)
    wr_en===1'b1 && rd2_addr==wr_addr); // same-cycle RAW hazard seen on port2
endmodule

// Bind into DUT
bind RegisterFile RegisterFile_sva rf_sva (.*);