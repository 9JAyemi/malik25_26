// SVA for rc4. Bind this file to the DUT.
// Focused, high-signal-coverage checks with concise properties.

bind rc4 rc4_sva u_rc4_sva();

module rc4_sva;

  // In bind scope we can directly reference DUT signals
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Basic combinational relation
  assert property (control_out == (count == keylength));

  // Reset effect (not disabled on reset edge)
  assert property (@(posedge clk) !rst_n |=> (i==8'h00 && j==8'h00 && count==8'h00 && streamvalue==8'h00));

  // No X on key outputs after reset releases
  assert property (!$isunknown(control_out));
  assert property (!$isunknown(streamvalue));

  // Count behavior
  assert property (write && !(control_in && (count==keylength)) |=> count == $past(count) + 8'h01);
  assert property (control_in && (count==keylength) |=> count == 8'h00);
  assert property (!write && !(control_in && (count==keylength)) |=> count == $past(count));

  // Guard illegal KSA start (division/mod by zero risk)
  assert property (control_in && (count==keylength) |-> (keylength != 8'h00));

  // When control_in asserted but not ready (count != keylength), no state-machine progress
  assert property (control_in && (count != keylength) && !write |=> (i==$past(i) && j==$past(j) && streamvalue==$past(streamvalue)));

  // Initialization effects when control_in && count==keylength
  assert property (control_in && (count==keylength) |=> (i==8'h00 && j==8'h00));
  // keystream is cleared
  genvar k;
  generate
    for (k=0; k<256; k++) begin : g_zero_ks
      assert property (control_in && (count==keylength) |=> keystream[k] == 8'h00);
    end
  endgenerate

  // Read path (no-control phase): compute streamvalue, bump i; no side-effects to memories or j/temp
  assert property (!control_in && read |=> 
      ( i == $past(i) + 8'h01 ) &&
      ( streamvalue == ($past(keystream[$past(i)]) ^ $past(plaintext[$past(i)])) ) &&
      ( j == $past(j) ) && ( temp == $past(temp) ) &&
      ( plaintext[$past(i)]  == $past(plaintext[$past(i)]) ) &&
      ( keystream[$past(i)]  == $past(keystream[$past(i)]) ) &&
      ( ciphertext[$past(i)] == $past(ciphertext[$past(i)]) ));

  // Process path (no-control, no-read): update i, memories, j, temp, and state swap as coded
  assert property (!control_in && !read |=> i == $past(i) + 8'h01);
  assert property (!control_in && !read |=> plaintext[$past(i)]  == $past(streamvalue));
  assert property (!control_in && !read |=> keystream[$past(i)]  == $past(state[$past(i)]));
  assert property (!control_in && !read |=> ciphertext[$past(i)] == ($past(keystream[$past(i)]) ^ $past(plaintext[$past(i)])));
  // j update (only meaningful when keylength!=0)
  assert property (!control_in && !read && (keylength!=8'h00) |=> 
      j == (( $past(j) + $past(state[$past(i)]) + $past(key[$past(i) % keylength]) ) & 8'hFF));
  // temp update
  assert property (!control_in && !read |=> temp == $past(state[$past(i)]));
  // state updates as coded (note: if i==j, the last NBA wins -> state[i] = temp)
  assert property (!control_in && !read |=> 
      state[$past(i)] == ( ($past(i)==$past(j)) ? $past(temp) : $past(state[$past(j)]) ));
  assert property (!control_in && !read |=> state[$past(j)] == $past(temp));

  // Sanity coverage
  cover property (write && (count==keylength-1));
  cover property (control_in && (count==keylength));
  cover property (!control_in && read);
  cover property (!control_in && !read);
  cover property ( ( (!control_in && read) || (!control_in && !read) ) && ($past(i)==8'hFF) |=> (i==8'h00) );

endmodule