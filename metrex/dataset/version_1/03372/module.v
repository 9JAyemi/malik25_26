
module i2c_master (
  input SCL,
  input SDA_OUT,
  output SDA_OUT_EN,
  input SDA_IN,
  output SDA_IN_EN,
  output ACK
);

  reg [7:0] data_out;
  reg [2:0] state;

  assign SDA_OUT_EN = (state == 1 || state == 2 || state == 4) ? 1 : 0;
  assign SDA_IN_EN = (state == 2 || state == 3 || state == 5) ? 1 : 0;

  assign ACK = (state == 3 || state == 5) ? ~SDA_IN : 1;

  always @(posedge SCL) begin
    case (state)
      0: begin // idle
        if (SDA_OUT == 0) begin
          state <= 1;
          data_out <= 8'b10100000; // slave address + write bit
        end
      end
      1: begin // start condition
        state <= 2;
      end
      2: begin // send slave address
        if (ACK == 0) begin
          state <= 3;
        end
      end
      3: begin // send data
        if (ACK == 0) begin
          state <= 4;
          data_out <= 8'b11000000; // slave address + read bit
        end
      end
      4: begin // repeated start condition
        state <= 5;
      end
      5: begin // receive data
        if (ACK == 0) begin
          state <= 6;
        end
      end
      6: begin // stop condition
        state <= 0;
      end
    endcase
  end

endmodule

module i2c_slave (
  input SCL,
  input SDA_IN,
  output SDA_OUT,
  output SDA_OUT_EN,
  input SDA_IN_EN,
  input ACK
);

  reg [7:0] data_in;
  reg [2:0] state;

  assign SDA_OUT_EN = (state == 2 || state == 4) ? 1 : 0;

  always @(posedge SCL) begin
    case (state)
      0: begin // idle
        if (SDA_IN == 0) begin
          state <= 1;
        end
      end
      1: begin // start condition
        state <= 2;
      end
      2: begin // receive slave address
        if (ACK == 0) begin
          state <= 3;
        end
      end
      3: begin // receive data
        if (ACK == 0) begin
          state <= 4;
        end
      end
      4: begin // send data
        state <= 5;
      end
      5: begin // stop condition
        state <= 0;
      end
    endcase
  end

  always @(posedge SCL) begin
    if (SDA_IN_EN) begin
      data_in <= {data_in[6:0], SDA_IN};
    end
  end

  assign SDA_OUT = data_in[7];

endmodule
