// SVA for sha256_W
// Bind this to the DUT (no ports; references DUT internals directly)
module sha256_W_sva;

  // Default clock and past-valid guard (no reset in DUT)
  default clocking cb @(posedge clk); endclocking
  logic past_valid; initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Helpers
  function automatic [31:0] data_idx_v(input [511:0] v, input int unsigned idx);
    return v[512 - (idx*32) - 1 -: 32];
  endfunction

  function automatic [31:0] sigma0(input [31:0] x);
    return {x[6:0],  x[31:7]}  ^ {x[17:0], x[31:18]} ^ {3'b0,   x[31:3]};
  endfunction

  function automatic [31:0] sigma1(input [31:0] x);
    return {x[16:0], x[31:17]} ^ {x[18:0], x[31:19]} ^ {10'b0,  x[31:10]};
  endfunction

  // Combinational tie-off
  assert property (1'b1 |-> (W_o == W[0]));

  // Register updates must match their combinational next values
  assert property (1'b1 |=> (h0 == $past(h0_new) && h1 == $past(h1_new)));

  // h0/h1 functional correctness (uses sigma on selected sources)
  assert property (1'b1 |=> 
    h0 == ( $past(load_i) ? ( sigma0(data_idx_v($past(data_i),1)) + data_idx_v($past(data_i),0) )
                          : ( sigma0($past(W[2]))               + $past(W[1]) ) ) );

  assert property (1'b1 |=> 
    h1 == ( $past(load_i) ? ( sigma1(data_idx_v($past(data_i),14)) + data_idx_v($past(data_i),9) )
                          : ( sigma1($past(W[15]))                 + $past(W[10]) ) ) );

  // Load: W[] loads from data_i (load has priority over busy)
  genvar li;
  generate
    for (li = 0; li < 16; li++) begin : gen_load_map
      assert property (load_i |=> W[li] == data_idx_v($past(data_i), li));
    end
  endgenerate

  // Busy shift: W[0..14] shift left; W[15] gets h0+h1
  genvar bi;
  generate
    for (bi = 0; bi < 15; bi++) begin : gen_busy_shift
      assert property (busy_i && !load_i |=> W[bi] == $past(W[bi+1]));
    end
  endgenerate
  assert property (busy_i && !load_i |=> W[15] == $past(h0 + h1));

  // Idle: when neither load nor busy, W[] zeroes
  genvar zi;
  generate
    for (zi = 0; zi < 16; zi++) begin : gen_idle_zero
      assert property (!load_i && !busy_i |=> W[zi] == 32'd0);
    end
  endgenerate

  // Explicit priority check when both asserted
  assert property (load_i && busy_i |=> W[15] == data_idx_v($past(data_i),15));

  // Minimal functional coverage
  cover property (load_i ##1 busy_i);
  cover property (busy_i && !load_i ##1 busy_i && !load_i ##1 busy_i && !load_i); // 3+ shift cycles
  cover property (!load_i && !busy_i);

endmodule

bind sha256_W sha256_W_sva u_sha256_W_sva();