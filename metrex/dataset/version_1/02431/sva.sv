// SVA for top_module (bind-in, no DUT edits required)
module top_module_sva;

  // This module is bound into top_module scope, so it can see:
  // decoder_in, alu_A, alu_B, alu_OP, final_output, decoder_out, alu_output

  // Helper local function
  function automatic bit is_onehot4 (logic [3:0] v);
    return (v == 4'b0001) || (v == 4'b0010) || (v == 4'b0100) || (v == 4'b1000);
  endfunction

  // Combinational checks and coverage
  always_comb begin
    // Basic X/Z checks
    assert (!$isunknown({decoder_in, alu_A, alu_B, alu_OP}))
      else $error("X/Z on inputs");
    assert (!$isunknown({decoder_out, alu_output, final_output}))
      else $error("X/Z on internal/outputs");

    // Decoder: exact mapping and one-hotness
    assert (decoder_out == (4'b0001 << decoder_in))
      else $error("Decoder mapping mismatch: in=%0b out=%0b", decoder_in, decoder_out);
    assert ($onehot(decoder_out))
      else $error("Decoder output not one-hot: %0b", decoder_out);

    // ALU: operation correctness (4-bit wrap on add/sub)
    unique case (alu_OP)
      3'b000: assert (alu_output == ((alu_A + alu_B) & 4'hF))
                else $error("ALU add mismatch");
      3'b001: assert (alu_output == ((alu_A - alu_B) & 4'hF))
                else $error("ALU sub mismatch");
      3'b010: assert (alu_output == (alu_A & alu_B))
                else $error("ALU and mismatch");
      3'b011: assert (alu_output == (alu_A | alu_B))
                else $error("ALU or mismatch");
      3'b100: assert (alu_output == (alu_A ^ alu_B))
                else $error("ALU xor mismatch");
      3'b101: assert (alu_output == (~alu_A))
                else $error("ALU not A mismatch");
      3'b110: assert (alu_output == (~alu_B))
                else $error("ALU not B mismatch");
      3'b111: assert (alu_output == 4'h0)
                else $error("ALU zero mismatch");
      default: assert (alu_output == 4'h0)
                else $error("ALU default mismatch");
    endcase

    // Top selection: final_output must mirror selected alu_output bit in bit[0]; upper bits zero
    assert (final_output[3:1] == 3'b000)
      else $error("final_output upper bits not zero: %0b", final_output);

    unique case (decoder_out)
      4'b0001: assert (final_output == {3'b000, alu_output[0]})
                 else $error("Select[0] mismatch");
      4'b0010: assert (final_output == {3'b000, alu_output[1]})
                 else $error("Select[1] mismatch");
      4'b0100: assert (final_output == {3'b000, alu_output[2]})
                 else $error("Select[2] mismatch");
      4'b1000: assert (final_output == {3'b000, alu_output[3]})
                 else $error("Select[3] mismatch");
      default: assert (final_output == 4'h0)
                 else $error("Default select mismatch");
    endcase

    // Lightweight functional coverage
    // Decoder inputs
    cover (decoder_in == 2'd0);
    cover (decoder_in == 2'd1);
    cover (decoder_in == 2'd2);
    cover (decoder_in == 2'd3);

    // ALU ops
    cover (alu_OP == 3'd0);
    cover (alu_OP == 3'd1);
    cover (alu_OP == 3'd2);
    cover (alu_OP == 3'd3);
    cover (alu_OP == 3'd4);
    cover (alu_OP == 3'd5);
    cover (alu_OP == 3'd6);
    cover (alu_OP == 3'd7);

    // Interesting ALU scenarios
    cover ((alu_OP == 3'b000) && ((alu_A + alu_B) > 4'hF)); // add overflow (wrap)
    cover ((alu_OP == 3'b001) && (alu_A <  alu_B));         // sub underflow (wrap)

    // Selection path coverage (both bit=1 and bit=0 per lane)
    cover (decoder_out == 4'b0001 && alu_output[0] == 1'b1);
    cover (decoder_out == 4'b0001 && alu_output[0] == 1'b0);
    cover (decoder_out == 4'b0010 && alu_output[1] == 1'b1);
    cover (decoder_out == 4'b0010 && alu_output[1] == 1'b0);
    cover (decoder_out == 4'b0100 && alu_output[2] == 1'b1);
    cover (decoder_out == 4'b0100 && alu_output[2] == 1'b0);
    cover (decoder_out == 4'b1000 && alu_output[3] == 1'b1);
    cover (decoder_out == 4'b1000 && alu_output[3] == 1'b0);
  end

endmodule

bind top_module top_module_sva sva_top_module();