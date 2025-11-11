// SVA for DataMemory
// Bind this file to the DUT: bind DataMemory DataMemory_sva dm_sva();

module DataMemory_sva;

  // Address decoder used by assertions/coverage
  function automatic int decode_addr (logic [31:0] a);
    case (a)
      32'h00000000: return 0;
      32'h00000004: return 1;
      32'h00000008: return 2;
      32'h0000000c: return 3;
      32'h00000010: return 4;
      32'h00000014: return 5;
      32'h00000018: return 6;
      32'h0000001c: return 7;
      32'h00000020: return 8;
      32'h00000024: return 9;
      default:       return -1;
    endcase
  endfunction

  // 1) Outputs mirror memory taps at all times
  assert property (@(posedge CLK or negedge CLK)
                   (DATO1 == block[4] && DATO2 == block[5] && RESULTADO == block[7]))
    else $error("Tap outputs mismatch memory contents");

  // 2) Read behavior when CLK==1
  assert property (@(posedge CLK)
                   (decode_addr(Address) >= 0) |-> (ReadData == block[decode_addr(Address)]))
    else $error("ReadData mismatch for valid address");
  assert property (@(posedge CLK)
                   (decode_addr(Address) < 0) |-> (ReadData == 32'h0))
    else $error("ReadData not zero on invalid address");
  assert property (@(posedge CLK)
                   (decode_addr(Address) >= 0) |-> !$isunknown(ReadData))
    else $error("ReadData has X/Z on valid address");

  // 3) Write behavior when CLK==0
  // Valid-address write
  assert property (@(negedge CLK)
                   (WriteEnable && decode_addr(Address) >= 0)
                   |-> (block[decode_addr(Address)] == WriteData))
    else $error("Write to memory did not land at decoded index");

  // Mouse write when not overridden by a write to block[1]
  assert property (@(negedge CLK)
                   (MouseEnable && !(WriteEnable && decode_addr(Address) == 1))
                   |-> (block[1] == MouseData))
    else $error("Mouse write to block[1] missing when not overridden");

  // Arbitration when both asserted and Address==0x4 (idx==1): WriteData wins
  assert property (@(negedge CLK)
                   (MouseEnable && WriteEnable && decode_addr(Address) == 1)
                   |-> (block[1] == WriteData))
    else $error("WriteEnable must override MouseEnable for block[1]");

  // Both asserted and Address!=0x4: mouse updates block[1], write updates its index
  assert property (@(negedge CLK)
                   (MouseEnable && WriteEnable && decode_addr(Address) >= 0 && decode_addr(Address) != 1)
                   |-> (block[1] == MouseData && block[decode_addr(Address)] == WriteData))
    else $error("Concurrent mouse+write incorrect when address != 0x4");

  // 4) Functional coverage
  // Read coverage for all legal addresses and default case
  generate
    genvar gi;
    for (gi = 0; gi < 10; gi++) begin : COV_RD
      cover property (@(posedge CLK)
                      (decode_addr(Address) == gi) && (ReadData == block[gi]));
    end
  endgenerate
  cover property (@(posedge CLK)
                  (decode_addr(Address) < 0) && (ReadData == 32'h0)); // default read

  // Write coverage for all legal addresses
  generate
    for (gi = 0; gi < 10; gi++) begin : COV_WR
      cover property (@(negedge CLK)
                      (WriteEnable && decode_addr(Address) == gi) && (block[gi] == WriteData));
    end
  endgenerate

  // Mouse-only write, and both-active precedence cases
  cover property (@(negedge CLK) MouseEnable && !WriteEnable && (block[1] == MouseData));
  cover property (@(negedge CLK) MouseEnable && WriteEnable && decode_addr(Address) == 1
                                && (block[1] == WriteData));
  cover property (@(negedge CLK) MouseEnable && WriteEnable && decode_addr(Address) >= 0
                                && decode_addr(Address) != 1
                                && (block[1] == MouseData)
                                && (block[decode_addr(Address)] == WriteData));

endmodule

bind DataMemory DataMemory_sva dm_sva();