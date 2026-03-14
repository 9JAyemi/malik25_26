
module digitalclock (
  input clk,
  input reset,
  output reg [3:0] hour,
  output reg [5:0] minute,
  output reg ampm, // 1 for PM, 0 for AM
  output reg valid // 1 if time is valid (12:00 PM)
);

  reg [3:0] hour_count;
  reg [5:0] minute_count;

  always @(posedge clk) begin
    if (reset) begin
      hour_count <= 4'b0001;
      minute_count <= 6'b000000;
    end else begin
      // increment minute count
      if (minute_count == 6'd59) begin
        minute_count <= 6'b000000;
        // increment hour count
        if (hour_count == 4'd12) begin
          hour_count <= 4'd01;
        end else begin
          hour_count <= hour_count + 1;
        end
      end else begin
        minute_count <= minute_count + 1;
      end

      // set valid flag if time is valid
      if (hour_count == 4'd12 && minute_count == 6'd00) begin
        valid <= 1'b1;
      end else begin
        valid <= 1'b0;
      end
    end
  end

  // output hour and minute counts
  always @(*) begin
    hour = hour_count;
    minute = minute_count;
  end

  // toggle AM/PM indicator every 12 hours
  always @(posedge clk) begin
    if (reset) begin
      ampm <= 1'b0;
    end else if (hour_count == 4'd12) begin
      ampm <= ~ampm;
    end
  end

endmodule