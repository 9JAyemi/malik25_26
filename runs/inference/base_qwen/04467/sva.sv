module RegisterAdd__parameterized5_sva
   #(parameter N = 23)
   (Q,
    E,
    D,
    CLK,
    AR);
  input [N-1:0]Q;
  input [0:0]E;
  input [N-1:0]D;
  input CLK;
  input [0:0]AR;

  reg [N-1:0]Q_reg;

  always @(posedge CLK or negedge AR)
  begin
    if (!AR) begin
      Q_reg <= {N{1'b0}};
    end
    else if (E) begin
      Q_reg <= D + Q_reg;
    end
  end

  assign Q = Q_reg;

  ///// Register reset /////
  // At reset assertion, the register Q_reg must be driven to 0.
  reset: assert property (
      @(posedge CLK) disable iff (!AR) (Q_reg == {N{1'b0}})
  );

  ///// Register update /////
  // When E is high, the register Q_reg must update to D + Q_reg.
  update: assert property (
      @(posedge CLK) disable iff (!AR) (E == 1'b1) |-> (Q_reg == D + Q_reg)
  );

  ///// Register hold /////
  // When E is low, the register Q_reg must not change.
  hold: assert property (
      @(posedge CLK) disable iff (!AR) (E == 1'b0) |-> (Q_reg == Q_reg)
  );

  ///// Register initialization /////
  // When AR is low, the register Q_reg must be initialized to 0.
  init: assert property (
      @(posedge CLK) disable iff (!AR) (AR == 1'b0) |-> (Q_reg == {N{1'b0}})
  );

  ///// Register final state /////
  // When AR is high, the register Q_reg must not change.
  final_state: assert property (
      @(posedge CLK) disable iff (!AR) (AR == 1'b1) |-> (Q_reg == Q_reg)
  );

endmodule