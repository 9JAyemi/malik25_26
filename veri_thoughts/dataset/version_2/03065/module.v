module IBUFDS_GTE3 #(
  parameter REFCLK_EN_TX_PATH = 1'b0,
  parameter REFCLK_HROW_CK_SEL = 2'b00,
  parameter REFCLK_ICNTL_RX = 2'b00
)(
  output reg O,
  output reg ODIV2,

  input CEB,
  input I,
  input IB
);

  reg [2:0] edge_count = 0;
  reg allEqual = 0;
  reg ODIV2_out = 0;

  always @(posedge I) begin
    if (CEB == 1'b0) begin
      edge_count <= edge_count + 1;
    end
  end

  always @(edge_count) begin
    if (edge_count == REFCLK_ICNTL_RX) begin
      allEqual <= 1;
    end else begin
      allEqual <= 0;
    end
  end

  always @(*) begin
    case (REFCLK_HROW_CK_SEL)
      2'b00: begin
        if (REFCLK_EN_TX_PATH || CEB == 1'b0) begin
          O <= 1'b0;
        end else begin
          O <= I;
        end
        ODIV2_out <= O;
      end
      2'b01: begin
        O <= I;
        if (allEqual == 1 || REFCLK_EN_TX_PATH || CEB == 1'b0) begin
          ODIV2_out <= 1'b0;
        end else begin
          ODIV2_out <= 1'b1;
        end
      end
      2'b10, 2'b11: begin
        O <= I;
        ODIV2_out <= 1'b0;
      end
    endcase
  end

  always @* begin
    ODIV2 = ODIV2_out;
  end

endmodule