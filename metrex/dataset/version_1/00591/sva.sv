// SVA checker for binary_up_counter
module binary_up_counter_sva #(parameter int n = 4)
(
  input logic                 clk,
  input logic [n-1:0]         out,
  input logic [n-1:0]         count
);
  localparam int unsigned MAX = (1<<n)-1;

  default clocking cb @(posedge clk); endclocking

  // Static sanity (catch parameter/width inconsistencies)
  initial assert ($bits(out)==n && $bits(count)==n)
    else $error("Width mismatch: n=%0d bits(out)=%0d bits(count)=%0d", n, $bits(out), $bits(count));

  function automatic bit known(input logic [n-1:0] v); return !$isunknown(v); endfunction

  // Out mirrors internal count
  a_out_mirror: assert property (out === count);

  // Deterministic next-state: +1 or wrap to 0 (only when previous state is known)
  a_inc:  assert property ( known($past(count)) && $past(count) != MAX |-> count == $past(count)+1 );
  a_wrap: assert property ( known($past(count)) && $past(count) == MAX |-> count == '0 );

  // Once known, stays known
  a_known: assert property ( known($past(count)) |-> known(count) );

  // Periodicity: after 2**n cycles, value repeats (from any known start)
  a_period: assert property ( known($past(count, MAX+1)) |-> count == $past(count, MAX+1) );

  // Coverage
  c_any_inc: cover property ( known($past(count)) && $past(count)!=MAX && count==$past(count)+1 );
  c_wrap:    cover property ( known($past(count)) && $past(count)==MAX && count=='0 );

  // Hit every state at least once
  genvar k;
  generate
    for (k=0; k<=MAX; k++) begin : C_STATES
      localparam int KK = k;
      localparam logic [n-1:0] K = KK[n-1:0];
      c_state: cover property (count == K);
    end
  endgenerate
endmodule

// Bind into DUT (connects to internal 'count')
bind binary_up_counter binary_up_counter_sva #(.n(n)) u_sva (.clk(clk), .out(out), .count(count));