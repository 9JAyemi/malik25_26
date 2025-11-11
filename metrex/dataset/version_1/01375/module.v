module averager_counter (
  input        restart,
  input        clken,
  input [31:0] count_max,
  input        clk,
  input        avg_on,
  output       clr_fback,
  output       ready,
  output       wen,
  output       avg_on_out,
  output [31:0] n_avg,
  output [31:0] address
);

  parameter N = 4; // number of values to average (must be a power of 2)
  parameter WIDTH = $clog2(N); // number of bits needed to represent N
  parameter AVG_WIDTH = 2*WIDTH + $clog2(32); // number of bits needed to represent the average

  reg [WIDTH-1:0]  index; // index of the current value in the averaging buffer
  reg [31:0]       sum;   // sum of the last N values of the counter
  reg [AVG_WIDTH-1:0] avg; // current average value
  
  reg [31:0] count; // current value of the counter
  reg [31:0] next_count; // next value of the counter (after incrementing)
  reg [31:0] max_count; // maximum value of the counter
  
  reg avg_on_reg; // register to store the value of avg_on
  reg [WIDTH-1:0]  wen_cnt; // counter to track the number of values written to the averaging buffer
  wire wen_int; // internal signal to indicate when the averaging buffer is ready to receive a new value
  wire ready_int; // internal signal to indicate when the averaging function has calculated a new average value
  
  assign clr_fback = (count == count_max); // clear the counter when it reaches its maximum value
  assign address = count; // output the current value of the counter
  
  // increment the counter on each clock cycle
  always @(posedge clk) begin
    if (restart) begin
      count <= 0;
    end else if (clken) begin
      if (count == count_max) begin
        count <= 0;
      end else begin
        count <= count + 1;
      end
    end
  end
  
  // calculate the next value of the counter (after incrementing)
  always @(*) begin
    if (count == count_max) begin
      next_count = 0;
    end else begin
      next_count = count + 1;
    end
  end
  
  // calculate the maximum value of the counter
  always @(*) begin
    max_count = count_max;
  end
  
  // enable or disable the averaging function
  always @(posedge clk) begin
    if (restart) begin
      avg_on_reg <= 0;
    end else if (clken) begin
      avg_on_reg <= avg_on;
    end
  end
  
  // calculate the sum of the last N values of the counter
  always @(posedge clk) begin
    if (restart) begin
      sum <= 0;
    end else if (clken) begin
      if (count == count_max) begin
        sum <= 0;
      end else begin
        sum <= sum + count - (wen_int ? avg[N-1] : 0);
      end
    end
  end
  
  // calculate the current average value
  always @(posedge clk) begin
    if (restart) begin
      avg <= 0;
    end else if (clken) begin
      if (count == count_max) begin
        avg <= 0;
      end else if (wen_int) begin
        avg <= {sum[N-1:0], wen_cnt, count};
      end
    end
  end
  
  // write the current value of the counter to the averaging buffer
  always @(posedge clk) begin
    if (restart) begin
      index <= 0;
      wen_cnt <= 0;
    end else if (clken) begin
      if (wen_int) begin
        index <= index + 1;
        wen_cnt <= wen_cnt + 1;
      end
    end
  end
  
  // check if the averaging buffer is ready to receive a new value
  assign wen_int = (wen_cnt < N);
  
  // check if the averaging function has calculated a new average value
  assign ready_int = (wen_cnt == N);
  
  // output the current average value
  assign n_avg = avg[N-1:0];
  
  // output the control signals
  assign wen = wen_int && avg_on_reg;
  assign ready = ready_int;
  assign avg_on_out = avg_on_reg;
  
endmodule