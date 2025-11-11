// SVA checker for key_gen
// Bind to DUT instance and connect a clock from your TB.
module key_gen_sva (
  input logic                clk,
  input logic [55:0]         previous_key,
  input logic [3:0]          iteration,
  input logic                decrypt,
  input logic [55:0]         non_perm_key,
  input logic [47:0]         new_key
);

  default clocking cb @(posedge clk); endclocking

  // Helpers
  function automatic [27:0] rotl28 (input [27:0] x, input int unsigned k_in);
    int unsigned k;
    begin
      k = k_in % 28;
      if (k == 0) rotl28 = x;
      else rotl28 = ((x << k) | (x >> (28 - k))) & 28'h0FFFFFFF;
    end
  endfunction

  function automatic int unsigned rotl_k (input bit dec, input logic [3:0] it);
    if (!dec)                       rotl_k = (it inside {4'd0,4'd1,4'd8,4'd15}) ? 1 : 2;
    else if (it == 4'd0)            rotl_k = 0;         // no shift on first decrypt round
    else if (it inside {4'd1,4'd8,4'd15}) rotl_k = 27;  // right 1 = left 27
    else                            rotl_k = 26;        // right 2 = left 26
  endfunction

  function automatic [55:0] exp_non_perm (
      input [55:0] pk, input logic [3:0] it, input bit dec);
    int unsigned k;
    begin
      k = rotl_k(dec, it);
      exp_non_perm = { rotl28(pk[55:28], k), rotl28(pk[27:0], k) };
    end
  endfunction

  function automatic [47:0] pc2 (input [55:0] np);
    pc2 = {
      np[42], np[39], np[45], np[32],
      np[55], np[51], np[53], np[28],
      np[41], np[50], np[35], np[46],
      np[33], np[37], np[44], np[52],
      np[30], np[48], np[40], np[49],
      np[29], np[36], np[43], np[54],
      np[15], np[4],  np[25], np[19],
      np[9],  np[1],  np[26], np[16],
      np[5],  np[11], np[23], np[8],
      np[12], np[7],  np[17], np[0],
      np[22], np[3],  np[10], np[14],
      np[6],  np[20], np[27], np[24]
    };
  endfunction

  // Functional correctness
  assert property ( non_perm_key == exp_non_perm(previous_key, iteration, decrypt) )
    else $error("non_perm_key mismatch with expected rotation");

  assert property ( new_key == pc2(non_perm_key) )
    else $error("new_key mismatch with PC2(permuted key)");

  // End-to-end check (redundant but tight)
  assert property ( new_key == pc2(exp_non_perm(previous_key, iteration, decrypt)) )
    else $error("End-to-end mismatch: new_key != PC2(rotate(previous_key))");

  // X-propagation safety
  assert property ( !$isunknown({previous_key, iteration, decrypt}) |-> !$isunknown({non_perm_key, new_key}) )
    else $error("X/Z detected on outputs with known inputs");

  // Minimal wrap-around spot checks per mode (boundary sanity)
  // Left rotate by 1 group
  assert property ( !decrypt && (iteration inside {4'd0,4'd1,4'd8,4'd15}) |->
                    non_perm_key[55:28][27] == previous_key[55:28][26] &&
                    non_perm_key[55:28][0]  == previous_key[55:28][27] )
    else $error("Left-1 wrap check failed (left half)");
  // Left rotate by 2 group
  assert property ( !decrypt && !(iteration inside {4'd0,4'd1,4'd8,4'd15}) |->
                    non_perm_key[55:28][27:26] == previous_key[55:28][25:24] &&
                    non_perm_key[55:28][1:0]   == previous_key[55:28][27:26] )
    else $error("Left-2 wrap check failed (left half)");
  // Decrypt no-shift (iter==0)
  assert property ( decrypt && (iteration==4'd0) |->
                    non_perm_key == previous_key )
    else $error("Decrypt iter0 no-shift failed");
  // Right rotate by 1 group
  assert property ( decrypt && (iteration inside {4'd1,4'd8,4'd15}) |->
                    non_perm_key[55:28][27] == previous_key[55:28][0] )
    else $error("Right-1 wrap check failed (left half)");
  // Right rotate by 2 group
  assert property ( decrypt && !(iteration inside {4'd0,4'd1,4'd8,4'd15}) |->
                    non_perm_key[55:28][27:26] == previous_key[55:28][1:0] )
    else $error("Right-2 wrap check failed (left half)");

  // Coverage: exercise all schedule modes
  cover property ( !decrypt && (iteration inside {4'd0,4'd1,4'd8,4'd15}) );
  cover property ( !decrypt && !(iteration inside {4'd0,4'd1,4'd8,4'd15}) );
  cover property (  decrypt && (iteration==4'd0) );
  cover property (  decrypt && (iteration inside {4'd1,4'd8,4'd15}) );
  cover property (  decrypt && !(iteration inside {4'd0,4'd1,4'd8,4'd15}) );

  // Coverage: boundary wrap activity (different MSB/LSB to ensure wrap contribution)
  cover property ( !decrypt && (iteration inside {4'd0,4'd1,4'd8,4'd15}) &&
                   previous_key[55] != previous_key[28] );
  cover property (  decrypt && (iteration inside {4'd1,4'd8,4'd15}) &&
                   previous_key[28] != previous_key[55] );

endmodule

// Example bind (adjust clk path as appropriate):
// bind key_gen key_gen_sva u_key_gen_sva (
//   .clk(tb_clk),
//   .previous_key(previous_key),
//   .iteration(iteration),
//   .decrypt(decrypt),
//   .non_perm_key(non_perm_key),
//   .new_key(new_key)
// );