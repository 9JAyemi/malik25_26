// SVA checker for priority_encoder/top_module.
// Provide a sampling clock from your TB when binding.

module pe_sva (
  input logic        clk,      // sampling clock
  input logic [7:0]  in,
  input logic [2:0]  pos
);
  default clocking cb @(posedge clk); endclocking

  // Golden combinational model (4-state tolerant via casez)
  function automatic [2:0] enc8 (input logic [7:0] a);
    unique casez (a)
      8'b1???????: enc8 = 3'd7;
      8'b01??????: enc8 = 3'd6;
      8'b001?????: enc8 = 3'd5;
      8'b0001????: enc8 = 3'd4;
      8'b00001???: enc8 = 3'd3;
      8'b000001??: enc8 = 3'd2;
      8'b0000001?: enc8 = 3'd1;
      8'b00000000: enc8 = 3'd0;
      default:      enc8 = 3'bxxx; // unknown inputs allowed to yield X
    endcase
  endfunction

  // Correctness for all 0/1 inputs
  assert property (!$isunknown(in) |-> (pos == enc8(in)))
    else $error("priority_encoder: pos != expected encoding");

  // Output must be known when inputs are known
  assert property (!$isunknown(in) |-> !$isunknown(pos))
    else $error("priority_encoder: X/Z on pos for known in");

  // Functional coverage: exercise each winning priority and key corners
  genvar i;
  // Each priority case where bit i wins (no higher bits set)
  generate for (i = 0; i < 8; i++) begin : cov_hi_win
    cover property ( (in[i] && !(|in[7:i+1])) && (pos == i[2:0]) );
  end endgenerate
  // Multi-bit cases where i wins despite lower bits set
  generate for (i = 1; i < 8; i++) begin : cov_hi_with_lower
    cover property ( (in[i] && |in[i-1:0] && !(|in[7:i+1])) && (pos == i[2:0]) );
  end endgenerate
  // All-zero and all-ones corners
  cover property (in == 8'h00 && pos == 3'd0);
  cover property (in == 8'hFF && pos == 3'd7);
endmodule

// Example binds (replace tb_clk with your TB clock signal)
bind priority_encoder pe_sva pe_chk (.clk(tb_clk), .in(in), .pos(pos));
bind top_module       pe_sva top_chk(.clk(tb_clk), .in(in), .pos(pos));