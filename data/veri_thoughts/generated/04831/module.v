
module d_ff_async_reset_sync_set (
  input D,
  input C,
  input R,
  input E,
  output Q
);

  reg Q_next;

  always @ (posedge C or negedge E) begin
    if (!E) begin
      Q_next <= Q_next;
    end else if (R) begin
      Q_next <= 1'b0;
    end else begin
      Q_next <= D;
    end
  end

  assign Q = Q_next;

endmodule