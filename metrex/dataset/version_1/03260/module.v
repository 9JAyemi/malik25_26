module KeyBoardController(
  input wire clk,
  input wire PS2C,
  input wire PS2D,
  input wire InteAccept,
  output reg[15:0] scanCode,
  output reg KeyBoardInte
);

  reg[7:0] buffer[15:0]; // buffer to store scan codes
  reg[3:0] put, get; // put and get pointers for buffer
  reg[3:0] state; // state machine state
  reg[22:0] count; // counter for PS2 clock
  reg PS2Cf, PS2Df; // filtered PS2 signals
  reg [7:0] ps2c_filter, ps2d_filter; // PS2 signal filters
  reg [10:0] shift1, shift2; // shift registers for PS2 data
  reg new; // flag for new scan code

  initial begin
    put <= 0; 
    get <= 0;
    ps2c_filter <= 0;
    ps2d_filter <= 0;
    PS2Cf <= 1;
    PS2Df <= 1;
    shift1 <= 0;
    shift2 <= 0;
    state <= 0;
    count <= 0;
    new <= 0;
    KeyBoardInte <= 0;
  end

  always @(posedge clk) begin
    // filter PS2 signals and count clock cycles
    ps2c_filter[7] <= PS2C;
    ps2c_filter[6:0] <= ps2c_filter[7:1];
    ps2d_filter[7] <= PS2D;
    ps2d_filter[6:0] <= ps2d_filter[7:1];
    if (ps2c_filter == 8'b11111111)
      PS2Cf <= 1;
    else begin
      if (ps2c_filter == 8'b00000000)
        PS2Cf <= 0;
    end

    if (ps2d_filter == 8'b11111111)
      PS2Df <= 1;
    else begin
      if (ps2d_filter == 8'b00000000)
        PS2Df <= 0;
    end
    if (PS2Df) begin
      count <= count + 1;
    end
    else begin
      count <= 1;
    end
    if (state == 10) begin
      new <= 1;
    end
    if ((state == 0) && new) begin
      if (put != get-1) begin
        buffer[put] <= shift1[8:1];
        put <= put+1;
        new <= 0;
      end
    end
    if ((get == put) | InteAccept) begin
      KeyBoardInte <= 0;
    end
    else begin
      if (KeyBoardInte == 0) begin
        scanCode <= buffer[get];
        KeyBoardInte <= 1;
      end
    end
    if (InteAccept & (get != put)) begin
      get <= get + 1;
    end
  end

  wire rst;
  assign rst = (count == 0);

  // state machine for PS2 data
  always @(negedge PS2Cf or posedge rst) begin
    if (rst) begin
      state <= 0;
    end
    else begin
      shift1 <= {PS2Df, shift1[10:1]};
      shift2 <= {shift1[0], shift2[10:1]}; // send high byte first, then low byte

      if (state == 0 && PS2Df == 0) begin
        state <= 1;
      end
      else if (state == 10) begin
        state <= 0;
      end
      else begin
        state <= state + 1;
      end
    end
  end

endmodule