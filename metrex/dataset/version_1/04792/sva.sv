// SVA for MemoryArbiter (combinational checks, concise, high-signal coverage)
// Bind this module to the DUT; no clock/reset required.

module MemoryArbiter_sva #(parameter int n = 4) (
  input logic [n-1:0] mem_req,
  input logic [n-1:0] mem_ack,
  input logic [n-1:0] mem_req_out,
  input logic [n-1:0] mem_ack_out
);

  // Static design sanity
  initial begin
    assert (n == 4)
      else $error("MemoryArbiter_sva: n must be 4 for this implementation.");
  end

  // Combinational assertions and coverage
  always_comb begin
    automatic logic [n-1:0] pr;
    automatic logic [n-1:0] exp_req_out, exp_ack_out;
    automatic int idx;

    // Derived priority vector (matches DUT's bit ordering)
    pr = {mem_req[0] & mem_ack[0],
          mem_req[1] & mem_ack[1],
          mem_req[2] & mem_ack[2],
          mem_req[3] & mem_ack[3]};

    // Highest-priority select per DUT's case encoding
    idx = -1;
    unique case (pr)
      4'b1000: idx = 0;
      4'b0100: idx = 1;
      4'b0010: idx = 2;
      4'b0001: idx = 3;
      default: idx = -1;
    endcase

    // Expected outputs
    exp_req_out = '0;
    exp_ack_out = '0;
    if (idx != -1) begin
      exp_req_out[idx] = mem_req[idx];
      exp_ack_out[idx] = mem_ack[idx];
    end

    // No X/Z on I/O
    assert (!$isunknown({mem_req, mem_ack, mem_req_out, mem_ack_out}))
      else $error("MemoryArbiter_sva: X/Z detected on ports.");

    // Functional correctness of arbitration and routing
    assert (mem_req_out === exp_req_out)
      else $error("MemoryArbiter_sva: mem_req_out mismatch. exp=%b got=%b", exp_req_out, mem_req_out);

    assert (mem_ack_out === exp_ack_out)
      else $error("MemoryArbiter_sva: mem_ack_out mismatch. exp=%b got=%b", exp_ack_out, mem_ack_out);

    // Structural/safety properties
    assert ($onehot0(mem_req_out))
      else $error("MemoryArbiter_sva: mem_req_out not onehot0: %b", mem_req_out);

    assert ($onehot0(mem_ack_out))
      else $error("MemoryArbiter_sva: mem_ack_out not onehot0: %b", mem_ack_out);

    assert ((mem_req_out & ~mem_req) == '0)
      else $error("MemoryArbiter_sva: mem_req_out must be subset of mem_req.");

    assert ((mem_ack_out & ~mem_ack) == '0)
      else $error("MemoryArbiter_sva: mem_ack_out must be subset of mem_ack.");

    assert ((mem_ack_out & ~mem_req_out) == '0)
      else $error("MemoryArbiter_sva: mem_ack_out can only assert on selected request bit.");

    // Functional coverage
    cover (pr == 4'b1000 && mem_req_out == 4'b0001 && mem_ack_out[0] == mem_ack[0]);
    cover (pr == 4'b0100 && mem_req_out == 4'b0010 && mem_ack_out[1] == mem_ack[1]);
    cover (pr == 4'b0010 && mem_req_out == 4'b0100 && mem_ack_out[2] == mem_ack[2]);
    cover (pr == 4'b0001 && mem_req_out == 4'b1000 && mem_ack_out[3] == mem_ack[3]);
    cover (pr == '0 && mem_req_out == '0 && mem_ack_out == '0);                 // no candidate -> idle
    cover ($countones(pr) >= 2 && mem_req_out == '0 && mem_ack_out == '0);       // multi-candidate -> default/none
  end

endmodule

// Bind into DUT
bind MemoryArbiter MemoryArbiter_sva #(.n(n)) arb_sva (
  .mem_req     (mem_req),
  .mem_ack     (mem_ack),
  .mem_req_out (mem_req_out),
  .mem_ack_out (mem_ack_out)
);