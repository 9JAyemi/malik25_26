module flip_flop (
  input clk,
  input rst,
  input data,
  output reg q,
  output reg q_bar
);

parameter type = 0; // flip-flop type (D, JK, T, or SR)

always @(posedge clk) begin
  if (rst) begin
    q <= (type == 1 || type == 3) ? 1'b1 : 1'b0;
    q_bar <= (type == 1 || type == 3) ? 1'b0 : 1'b1;
  end else begin
    case (type)
      0: begin
        q <= data;
        q_bar <= ~data;
      end
      1: begin
        if (data) begin
          q <= ~q_bar;
          q_bar <= ~q;
        end else begin
          q <= q;
          q_bar <= q_bar;
        end
      end
      2: begin
        if (data) begin
          q <= ~q;
          q_bar <= ~q_bar;
        end else begin
          q <= q;
          q_bar <= q_bar;
        end
      end
      3: begin
        if (data) begin
          q <= (q_bar) ? 1'b0 : 1'b1;
          q_bar <= (q) ? 1'b0 : 1'b1;
        end else begin
          q <= q;
          q_bar <= q_bar;
        end
      end
    endcase
  end
end

endmodule