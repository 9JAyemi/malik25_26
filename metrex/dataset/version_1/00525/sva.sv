// SVA checker for RAM. Bind this to the DUT.
module RAM_sva #(parameter AW=7, DW=32, DEPTH=(1<<AW)) (
  input logic                 clka,
  input logic                 wea,
  input logic [AW-1:0]        addra,
  input logic [DW-1:0]        dina,
  input logic [DW-1:0]        douta
);

  // Simple golden model (mirrors DUT semantics: read-before-write, 1-cycle registered read)
  logic [DW-1:0] model [0:DEPTH-1];

  // Core functional check: douta equals previous-cycle memory value at current address
  // Update model after checking to keep timing aligned.
  always_ff @(posedge clka) begin
    assert (douta === model[addra])
      else $error("RAM rd-data mismatch: addr=%0d exp=%h got=%h", addra, model[addra], douta);
    if (wea) model[addra] = dina;
  end

  // RAW latency: write followed by reading same address next cycle returns the written data
  property p_write_then_read_same_addr_next;
    @(posedge clka) wea ##1 (addra == $past(addra)) |-> (douta === $past(dina));
  endproperty
  assert property (p_write_then_read_same_addr_next)
    else $error("RAW latency violation (write->read same addr)");

  // Basic X-checks on control/address (optional, tighten as needed)
  property p_ctrl_no_x;
    @(posedge clka) !$isunknown(wea) && !$isunknown(addra);
  endproperty
  assert property (p_ctrl_no_x) else $error("X on control/address");

  // Coverage
  localparam int LAST = DEPTH-1;
  cover property (@(posedge clka) wea);                                            // any write
  cover property (@(posedge clka) wea ##1 (addra == $past(addra)));                // write -> read same addr
  cover property (@(posedge clka) wea ##1 (addra != $past(addra)));                // write -> read different addr
  cover property (@(posedge clka) wea && addra == '0);                             // write to addr 0
  cover property (@(posedge clka) wea && addra == LAST);                           // write to last addr
  cover property (@(posedge clka) wea ##1 (wea && addra == $past(addra)));         // back-to-back writes same addr
  cover property (@(posedge clka) wea ##1 (wea && addra != $past(addra)));         // back-to-back writes different addr

endmodule

// Bind into the DUT
bind RAM RAM_sva #(.AW(7), .DW(32), .DEPTH(128)) u_ram_sva (
  .clka(clka), .wea(wea), .addra(addra), .dina(dina), .douta(douta)
);