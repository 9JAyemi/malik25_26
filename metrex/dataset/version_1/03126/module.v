
module TrafficSignalController(
  input clk,
  input NS_VEHICLE_DETECT,
  input EW_VEHICLE_DETECT,
  output reg NS_RED,
  output reg NS_YELLOW,
  output reg NS_GREEN,
  output reg EW_RED,
  output reg EW_YELLOW,
  output reg EW_GREEN
);

  // Counters
  reg[4:0] count1;
  reg[3:0] count2;
  reg[1:0] count3;

  // Counter Modules
  always @(posedge clk) begin
    if (count1 == 31) count1 <= 0;
    else count1 <= count1 + 1;
  end

  always @(posedge clk) begin
    if (count2 == 15) count2 <= 0;
    else if (EW_VEHICLE_DETECT) count2 <= count2 - 6;
      else count2 <= count2 + 1;
  end

  always @(posedge clk) begin
    if (count3 == 3) count3 <= 0;
    else count3 <= count3 + 1;
  end

  // Main Traffic Module
  always @(posedge clk) begin
    if (count3 == 3) begin
      // Yellow light
      NS_YELLOW <= 1'b1;
      EW_YELLOW <= 1'b1;
      NS_GREEN <= 1'b0;
      EW_GREEN <= 1'b0;
      NS_RED <= 1'b0;
      EW_RED <= 1'b0;
    end
    else if (count2 == 15) begin
      // EW green light
      NS_YELLOW <= 1'b0;
      EW_YELLOW <= 1'b0;
      NS_GREEN <= 1'b0;
      EW_GREEN <= 1'b1;
      NS_RED <= 1'b1;
      EW_RED <= 1'b0;
    end
    else if (count1 == 31) begin
      // NS green light
      NS_YELLOW <= 1'b0;
      EW_YELLOW <= 1'b0;
      NS_GREEN <= 1'b1;
      EW_GREEN <= 1'b0;
      NS_RED <= 1'b0;
      EW_RED <= 1'b1;
    end
    else begin
      // Red light
      NS_YELLOW <= 1'b0;
      EW_YELLOW <= 1'b0;
      NS_GREEN <= 1'b0;
      EW_GREEN <= 1'b0;
      NS_RED <= 1'b1;
      EW_RED <= 1'b1;
    end
  end

endmodule