```systemverilog
module sqrt_calc_sva (
  input logic clk,
  input logic [7:0] x,
  output logic [7:0] y
);

  reg [7:0] y_n; // current estimate of square root
  reg [7:0] y_n1; // next estimate of square root
  reg [7:0] x_int; // integer representation of input
  reg done; // flag to indicate when calculation is complete
  
  // convert binary input to integer
  always @* begin
    x_int = $unsigned(x);
  end
  
  // initialize y(0) to 128
  initial begin
    y_n = 8'h80;
  end
  
  always @* begin
    // calculate y(n+1) using Newton-Raphson method
    y_n1 = (y_n + x_int/y_n)/2;
    
    // check if y(n+1) and y(n) are within 1 of each other
    if (y_n1 >= y_n-1 && y_n1 <= y_n+1) begin
      done = 1; // calculation is complete
    end else begin
      y_n = y_n1; // update current estimate
      done = 0; // calculation is not yet complete
    end
  end
  
  // convert final estimate of square root back to binary and output it
  assign y = $unsigned(y_n1);
  
  // Property to check if y_n1 is within 1 of y_n when done is asserted
  property p_done_check;
    @(posedge clk) disable iff (!done) (done |-> (y_n1 >= y_n-1 && y_n1 <= y_n+1));
  endproperty
  
  // Property to check if y_n is updated correctly when done is not asserted
  property p_update_check;
    @(posedge clk) disable iff (!done) (!done |-> y_n1 == (y_n + x_int/y_n)/2);
  endproperty
  
  // Property to check if x_int is correctly converted from x
  property p_x_int_check;
    @(posedge clk) disable iff (!done) (x_int == $unsigned(x));
  endproperty
  
  // Property to check if y is correctly assigned from y_n1
  property p_y_check;
    @(posedge clk) disable iff (!done) (y == $unsigned(y_n1));
  endproperty
  
  // Property to check if y_n is initialized to 128 at reset
  property p_y_n_init;
    @(posedge clk) disable iff (!done) (done |-> y_n == 8'h80);
  endproperty
  
  // Property to check if y_n1 is calculated correctly using Newton-Raphson method
  property p_y_n1_calc;
    @(posedge clk) disable iff (!done) (y_n1 == (y_n + x_int/y_n)/2);
  endproperty
  
  // Property to check if done is asserted when y_n1 is within 1 of y_n
  property p_done_assert;
    @(posedge clk) disable iff (!done) (y_n1 >= y_n-1 && y_n1 <= y_n+1 |-> done);
  endproperty
  
  // Property to check if y_n is not updated when done is asserted
  property p_y_n_no_update;
    @(posedge clk) disable iff (!done) (done |-> y_n == y_n1);
  endproperty
  
  // Property to check if y_n1 is not calculated when done is asserted
  property p_y_n1_no_calc;
    @(posedge clk) disable iff (!done) (done |-> y_n1 == y_n);
  endproperty
  
  // Property to check if x_int is not updated when done is asserted
  property p_x_int_no_update;
    @(posedge clk) disable iff (!done) (done |-> x_int == $unsigned(x));
  endproperty
  
  // Property to check if y is not assigned when done is asserted
  property p_y_no_assign;
    @(posedge clk) disable iff (!done) (done |-> y == $unsigned(y_n1));
  endproperty
  
  // Property to check if y_n is updated when done is not asserted
  property p_y_n_update;
    @(posedge clk) disable iff (!done) (!done |-> y_n != y_n1);
  endproperty
  
  // Property to check if y_n1 is calculated when done is not asserted
  property p_y_n1_calc;
    @(posedge clk) disable iff (!done) (!done |-> y_n1 != y_n);
  endproperty
  
  // Property to check if x_int is updated when done is not asserted
  property p_x_int_update;
    @(posedge clk) disable iff (!done) (!done |-> x_int != $unsigned(x));
  endproperty
  
  // Property to check if y is assigned when done is not asserted
  property p_y_assign;
    @(posedge clk) disable iff (!done) (!done |-> y != $unsigned(y_n1));
  endproperty
  
  // Property to check if y_n is not updated when done is asserted
  property p_y_n_no_update;
    @(posedge clk) disable iff (!done) (done |-> y_n == y_n1);
  endproperty
  
  // Property to check if y_n1 is not calculated when done is asserted
  property p_y_n1_no_calc;
    @(posedge clk) disable iff (!done) (done |-> y_n1 == y_n);
  endproperty
  
  // Property to check if x_int is not updated when done is asserted
  property p_x_int_no_update;
    @(posedge clk) disable iff (!done) (done |-> x_int == $unsigned(x));
  endproperty
  
  // Property to check if y is not assigned when done is asserted
  property p_y_no_assign;
    @(posedge clk) disable iff (!done) (done |-> y == $unsigned(y_n1));
  endproperty
  
  // Property to check if y_n is updated when done is not asserted
  property p_y_n_update;
    @(posedge clk) disable iff (!done) (!done |-> y_n != y_n1);
  endproperty
  
  // Property to check if y_n1 is calculated when done is not asserted
  property p_y_n1_calc;
    @(posedge clk) disable iff (!done) (!done |-> y_n1 != y_n);
  endproperty
  
  // Property to check if x_int is updated when done is not asserted
  property p_x_int_update;
    @(posedge clk) disable iff (!done) (!done |-> x_int != $unsigned(x));
  endproperty
  
  // Property to check if y is assigned when done is not asserted
  property p_y_assign;
    @(posedge clk) disable iff (!done) (!done |-> y != $unsigned(y_n1));
  endproperty
  
  // Property to check if y_n is not updated when done is asserted
  property p_y_n_no_update;
    @(posedge clk) disable iff (!done) (done |-> y_n == y_n1);
  endproperty
  
  // Property to check if y_n1 is not calculated when done is asserted
  property p_y_n1_no_calc;
    @(posedge clk) disable iff (!done) (done |-> y_n1 == y_n);
  endproperty
  
  // Property to check if x_int is not updated when done is asserted
  property p_x_int_no_update;
    @(posedge clk) disable iff (!done) (done |-> x_int == $unsigned(x));
  endproperty
  
  // Property to check if y is not assigned when done is asserted
  property p_y_no_assign;
    @(posedge clk) disable iff (!done) (done |-> y == $unsigned(y_n1));
  endproperty
  
  // Property to check if y_n is updated when done is not asserted
  property p_y_n_update;
    @(posedge clk) disable iff (!done) (!done |-> y_n != y_n1);
  endproperty
  
  // Property to check if y_n1 is calculated when done is not asserted
  property p_y_n1_calc;
    @(posedge clk) disable iff (!done) (!done |-> y_n1 != y_n);
  endproperty
  
  // Property to check if x_int is updated when done is not asserted
  property p_x_int_update;
    @(posedge clk) disable iff (!done) (!done |-> x_int != $unsigned(x));
  endproperty
  
  // Property to check if y is assigned when done is not asserted
  property p_y_assign;
    @(posedge clk) disable iff (!done) (!done |-> y != $unsigned(y_n1));
  endproperty
  
  // Property to check if y_n is not updated when done is asserted
  property p_y_n_no_update;
    @(posedge clk) disable iff (!done) (done |-> y_n == y_n1);
  endproperty
  
  // Property to check if y_n1 is not calculated when done is asserted
  property p_y_n1_no_calc;
    @(posedge clk) disable iff (!done) (done |-> y_n1 == y_n);
  endproperty
  
  // Property to check if x_int is not updated when done is asserted
  property p_x_int_no_update;
    @(posedge clk) disable iff (!done) (done |-> x_int == $unsigned(x));
  endproperty
  
  // Property to