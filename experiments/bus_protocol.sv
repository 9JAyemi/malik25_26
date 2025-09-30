`timescale 1ns/1ps
`default_nettype none

// bus_protocol.sv
// Drives a simple data-valid / ack timing sequence for several scenarios.
// Intended as a stimulus/source for protocol assertions.
module bus_protocol (
    input  logic        clk,
    input  logic        reset,   // (not used by this stimulus; kept for interface completeness)
    output logic        dValid,
    output logic        dAck,
    output logic [7:0]  data
);

  initial begin
    // Initialize outputs
    dValid = 1'b0;
    dAck   = 1'b0;
    data   = 8'h00;

    $display("SCENARIO 1");
    @(negedge clk); dValid = 1'b0; data = 8'h00; dAck = 1'b0;
    @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
    @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
    @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b1;
    @(negedge clk); dValid = 1'b0; data = 8'h00; dAck = 1'b0;
    @(negedge clk); dValid = 1'b0; data = 8'h00; dAck = 1'b0;
    $display("");

    $display("SCENARIO 2");
    @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
    @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
    @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
    @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b1;
    @(negedge clk); dValid = 1'b0; data = 8'h00; dAck = 1'b0;
    @(negedge clk); dValid = 1'b0; data = 8'h00; dAck = 1'b0;
    $display("");

    $display("SCENARIO 3");
    @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
    @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
    @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
    @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
    @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b1;
    @(negedge clk); dValid = 1'b0; data = 8'h00; dAck = 1'b0;
    @(negedge clk); dValid = 1'b0; data = 8'h00; dAck = 1'b0;
    $display("");

    `ifdef nobugs
      $display("SCENARIO 4");
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b1;
      @(negedge clk); dValid = 1'b0; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b0; data = 8'h00; dAck = 1'b0;
      $display("");
    `else
      $display("SCENARIO 4");
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b1;
      @(negedge clk); dValid = 1'b0; data = 8'h00; dAck = 1'b0;
      $display("");
    `endif

    `ifdef nobugs
      $display("SCENARIO 5");
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b1;
      @(negedge clk); dValid = 1'b0; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b0; data = 8'h00; dAck = 1'b0;
      $display("");
    `else
      $display("SCENARIO 5");
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b1;
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b0; data = 8'h00; dAck = 1'b0;
      $display("");
    `endif

    `ifdef nobugs
      $display("SCENARIO 6");
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b1;
      @(negedge clk); dValid = 1'b0; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b0; data = 8'h00; dAck = 1'b0;
      $display("");
    `else
      $display("SCENARIO 6");
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b0; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b0; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b0; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b0; data = 8'h00; dAck = 1'b0;
      $display("");
    `endif

    `ifdef nobugs
      $display("SCENARIO 7");
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b1;
      @(negedge clk); dValid = 1'b0; data = 8'h00; dAck = 1'b0;
      $display("");
    `else
      $display("SCENARIO 7");
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b1; data = 8'hxx; dAck = 1'b1;
      @(negedge clk); dValid = 1'b0; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b0;
      @(negedge clk); dValid = 1'b1; data = 8'h01; dAck = 1'b0;
      @(negedge clk); dValid = 1'b1; data = 8'h00; dAck = 1'b1;
      @(negedge clk); dValid = 1'b0; data = 8'h00; dAck = 1'b0;
      @(negedge clk);
      @(negedge clk);
      $display("");
    `endif

    @(negedge clk);
    $finish(2);
  end

endmodule

`default_nettype wire
