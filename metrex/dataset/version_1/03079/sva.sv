// SVA/checkers for mod and mod5 (concise, quality-focused). Bind these to the DUT.

////////////////////////////////////////////////////////////
// Checker for mod5: Z must equal (A % 5 == 0)
module mod5_sva (input logic [4:0] A, input logic Z);
  // Functional correctness and no X on Z when A known
  always_comb begin
    if (!$isunknown(A)) begin
      assert (Z == ((A % 5) == 0))
        else $error("mod5: Z != (A %% 5 == 0). A=%0d Z=%0b", A, Z);

      // Coverage across all residues
      cover (A % 5 == 0 && Z);
      cover (A % 5 == 1 && !Z);
      cover (A % 5 == 2 && !Z);
      cover (A % 5 == 3 && !Z);
      cover (A % 5 == 4 && !Z);
    end
  end
endmodule

bind mod5 mod5_sva u_mod5_sva (.A(A), .Z(Z));

////////////////////////////////////////////////////////////
// Checker for mod: Z must equal (A[4:0] % 5 == 0) and be insensitive to A[7:5]
module mod_sva (input logic [7:0] A, input logic Z);
  // Functional correctness and no X on Z when low bits known
  always_comb begin
    if (!$isunknown(A[4:0])) begin
      assert (Z == ((A[4:0] % 5) == 0))
        else $error("mod: Z != (A[4:0] %% 5 == 0). A=%0h Z=%0b", A, Z);

      // Hit key multiples and edges
      cover (A[4:0] == 5'd0  && Z);
      cover (A[4:0] == 5'd1  && !Z);
      cover (A[4:0] == 5'd4  && !Z);
      cover (A[4:0] == 5'd5  && Z);
      cover (A[4:0] == 5'd10 && Z);
      cover (A[4:0] == 5'd15 && Z);
      cover (A[4:0] == 5'd20 && Z);
      cover (A[4:0] == 5'd25 && Z);
      cover (A[4:0] == 5'd30 && Z);
      cover (A[4:0] == 5'd31 && !Z);
    end
  end

  // Z must not change when only A[7:5] change (A[4:0] stable)
  logic [4:0] prev_low;
  logic [2:0] prev_hi;
  logic       prevZ;
  initial begin prev_low = 'x; prev_hi = 'x; prevZ = 'x; end

  always @(A or Z) begin
    if (!$isunknown(prev_low) && !$isunknown(prev_hi)) begin
      if (A[7:5] != prev_hi && A[4:0] == prev_low && !$isunknown(A[4:0])) begin
        assert (Z == prevZ)
          else $error("mod: Z changed when only upper bits changed. prevZ=%0b Z=%0b low=%0d",
                      prevZ, Z, prev_low);
      end
    end
    prev_low <= A[4:0];
    prev_hi  <= A[7:5];
    prevZ    <= Z;
  end

  // Simple toggle coverage on Z (observed behavior)
  always @(Z) begin
    if (!$isunknown(prevZ) && !$isunknown(Z)) begin
      if (prevZ==0 && Z==1) cover (1);
      if (prevZ==1 && Z==0) cover (1);
    end
    prevZ <= Z;
  end
endmodule

bind mod mod_sva u_mod_sva (.A(A), .Z(Z));