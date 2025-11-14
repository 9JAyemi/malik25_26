module Display(
  input clk,                 // clock signal
  input [15:0] num,          // number to display
  input [3:0] flash,         // flash signal
  output reg [7:0] display,  // 7-segment display control signal
  output reg [3:0] an        // digit selection signal
  );
  
  reg flash_state;  // current state of flashing, 1 => flashing
  reg [3:0] tmp;    // temporary variable for selecting digits
  reg [15:0] counter;  // counter for delaying digit selection
  reg [31:0] flash_counter;  // counter for delaying flashing
  
  // constants for setting counter limits
  parameter [15:0] MAX_COUNTER = 16'D5_0000;
  parameter [31:0] MAX_FLASH_COUNTER = 32'D5000_0000;
  
  // initialize variables
  initial begin
    tmp = 4'B0111;  // start with leftmost digit
    counter = 0;
    flash_counter = 0;
    flash_state = 0;
  end

  // always block for selecting which segments to display
  always@(tmp) begin
    case(tmp)
      4'B0111: display = num[15:12];  // leftmost digit
      4'B1011: display = num[11:8];   // second digit from left
      4'B1101: display = num[7:4];    // third digit from left
      4'B1110: display = num[3:0];    // rightmost digit
    endcase
    // segment values for each digit
    case(display)
      4'H0: display = 8'B0000_0011;
      4'H1: display = 8'B1001_1111;
      4'H2: display = 8'B0010_0101;
      4'H3: display = 8'B0000_1101;
      4'H4: display = 8'B1001_1001;
      4'H5: display = 8'B0100_1001;
      4'H6: display = 8'B0100_0001;
      4'H7: display = 8'B0001_1111;
      4'H8: display = 8'B0000_0001;
      4'H9: display = 8'B0000_1001;
    endcase
  end

  // always block for selecting which digit to display
  always@(posedge clk) begin
    // select next digit after delay
    counter = counter + 1;
    if(counter == MAX_COUNTER) begin
      tmp = (tmp >> 1) + 4'B1000;
      counter = 0;
    end
    // wrap back to leftmost digit after displaying rightmost digit
    if(tmp == 4'B1111) begin
      tmp = 4'B0111;
    end
    // alternate between flashing and non-flashing
    flash_counter = flash_counter + 1;
    if(flash_counter == MAX_FLASH_COUNTER) begin
      flash_counter = 0;
      flash_state = ~flash_state;
    end
    // set digit selection signal based on flash and current digit
    if(flash_state) an = tmp | flash;
    else an = tmp;
  end

endmodule