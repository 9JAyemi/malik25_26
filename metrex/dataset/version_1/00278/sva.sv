// SVA checker for module register
// Bind this checker to the DUT:  bind register register_sva chk(.*);

module register_sva(
  input clk,
  input Reset,
  input Write_Reg,
  input [4:0]  R_Addr_A, R_Addr_B, W_Addr,
  input [31:0] W_Data,
  input [31:0] R_Data_A, R_Data_B
);

  // Simple reference model (scoreboard)
  logic [31:0] rm [0:31];
  bit seen_reset;

  integer i;
  always @(posedge clk or posedge Reset) begin
    if (Reset) begin
      for (i=0;i<32;i++) rm[i] <= '0;
      seen_reset <= 1'b1;
    end else if (Write_Reg) begin
      rm[W_Addr] <= W_Data;
    end
  end

  // Basic sanity (no X on key controls/addr)
  assert property (@(posedge clk) !$isunknown({Reset,Write_Reg,R_Addr_A,R_Addr_B,W_Addr}));

  // During reset, outputs are zero
  assert property (@(posedge clk) Reset |-> (R_Data_A=='0 && R_Data_B=='0));

  // Read ports equality when same address
  assert property (@(posedge clk) (R_Addr_A==R_Addr_B) |-> (R_Data_A===R_Data_B));

  // Outputs match model (after model has been initialized by a reset)
  assert property (@(posedge clk) disable iff(!seen_reset)
    (1'b1 |-> (R_Data_A===rm[R_Addr_A] && R_Data_B===rm[R_Addr_B]))
  );

  // No-write-to-address -> stable read (1-cycle)
  assert property (@(posedge clk) disable iff(Reset)
    $stable(R_Addr_A) && !$past(Write_Reg && (W_Addr==$past(R_Addr_A)))
      |-> R_Data_A==$past(R_Data_A)
  );
  assert property (@(posedge clk) disable iff(Reset)
    $stable(R_Addr_B) && !$past(Write_Reg && (W_Addr==$past(R_Addr_B)))
      |-> R_Data_B==$past(R_Data_B)
  );

  // Write -> next-cycle readback on either port
  assert property (@(posedge clk) disable iff(Reset)
    Write_Reg ##1 (R_Addr_A==$past(W_Addr)) |-> (R_Data_A==$past(W_Data))
  );
  assert property (@(posedge clk) disable iff(Reset)
    Write_Reg ##1 (R_Addr_B==$past(W_Addr)) |-> (R_Data_B==$past(W_Data))
  );

  // Write while Reset high has no effect (model/output remain zero)
  assert property (@(posedge clk)
    Reset && Write_Reg |-> (R_Data_A=='0 && R_Data_B=='0)
  );

  // Coverage
  // See a reset
  cover property (@(posedge clk) $rose(Reset));
  // Write then read back on A
  cover property (@(posedge clk) disable iff(Reset)
    Write_Reg ##1 (R_Addr_A==$past(W_Addr) && R_Data_A==$past(W_Data))
  );
  // Write then read back on B
  cover property (@(posedge clk) disable iff(Reset)
    Write_Reg ##1 (R_Addr_B==$past(W_Addr) && R_Data_B==$past(W_Data))
  );
  // Both ports read same address
  cover property (@(posedge clk) (R_Addr_A==R_Addr_B));
  // Back-to-back writes to same address with different data, then readback
  property p_b2b_write_readback;
    int a; logic [31:0] d1,d2;
    @(posedge clk) disable iff(Reset)
      (Write_Reg, a=W_Addr, d1=W_Data)
      ##1 (Write_Reg && W_Addr==a && W_Data!=d1, d2=W_Data)
      ##1 ((R_Addr_A==a && R_Data_A==d2) || (R_Addr_B==a && R_Data_B==d2));
  endproperty
  cover property (p_b2b_write_readback);

endmodule

// Bind into DUT
bind register register_sva chk(.*);