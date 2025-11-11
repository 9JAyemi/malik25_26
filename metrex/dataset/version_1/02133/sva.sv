// SVA checker for module bar
// Focus: correctness of result for each sel, detect illegal sel drive, and concise coverage.

module bar_sva #(parameter OP_ADD = 2'b00)
(
  input logic [3:0] a,
  input logic [3:0] b,
  input logic [1:0] sel,
  input logic [3:0] result
);

  // Combinational immediate assertions (no clock in DUT)
  always @* begin
    // Inputs must be 2-state
    assert (!$isunknown({a,b,sel})) else $error("bar: X/Z on inputs");

    // sel is tied internally to OP_ADD; flag any contention/mismatch
    assert (sel == OP_ADD) else $error("bar: sel not equal to OP_ADD (possible multiple drivers)");

    // Functional correctness per opcode
    if (!$isunknown(sel)) begin
      unique case (sel)
        2'b00: assert (result == ((a + b) & 4'hF))
               else $error("bar ADD mismatch exp=%0h got=%0h", (a+b)&4'hF, result);
        2'b01: assert (result == ((a + (~b) + 1) & 4'hF)) // a - b (mod 16)
               else $error("bar SUB mismatch exp=%0h got=%0h", (a+(~b)+1)&4'hF, result);
        2'b10: assert (result == (a & b))
               else $error("bar AND mismatch exp=%0h got=%0h", (a&b), result);
        2'b11: assert (result == (a | b))
               else $error("bar OR mismatch exp=%0h got=%0h", (a|b), result);
      endcase
      // Result must be 2-state whenever sel is known
      assert (!$isunknown(result)) else $error("bar: X/Z on result for known sel");
    end else begin
      // If sel is X/Z, design default drives 0
      assert (result == 4'b0) else $error("bar: default result not 0 when sel is X/Z");
    end
  end

  // Lightweight functional coverage (immediate cover)
  always @* begin
    // Exercise all opcodes (these will show unreachable if sel is tied)
    cover (sel == 2'b00);
    cover (sel == 2'b01);
    cover (sel == 2'b10);
    cover (sel == 2'b11);

    // Corner cases
    cover (sel == 2'b00 && ((a + b) > 4'hF));     // ADD overflow
    cover (sel == 2'b01 && (a < b));              // SUB borrow
    cover (sel == 2'b10 && ((a & b) == 4'h0));    // AND yields zero
    cover (sel == 2'b11 && ((a | b) == 4'hF));    // OR yields all ones
  end

endmodule

// Bind into DUT
bind bar bar_sva #(.OP_ADD(OP_ADD)) u_bar_sva (.a(a), .b(b), .sel(sel), .result(result));