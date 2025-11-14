// Bind these SVA to your DUT without modifying it
bind asfifo_graycounter asfifo_graycounter_sva asfifo_graycounter_sva_i();

module asfifo_graycounter_sva ();

  // Use DUT scope directly (clk,rst,ce,gray_count,binary_count,width)
  default clocking cb @(posedge clk); endclocking

  // Parameter sanity
  initial assert (width >= 2) else $error("asfifo_graycounter: width must be >= 2");

  // Async reset takes effect immediately on posedge rst
  assert property (@(posedge rst) ##0 (binary_count == 'd1 && gray_count == '0));

  // While rst is held high, registers remain in reset on every clk
  assert property (rst |-> (binary_count == 'd1 && gray_count == '0));

  // No X/Z after reset deasserted
  assert property (disable iff (rst) !$isunknown({binary_count, gray_count}));

  // Hold when ce=0
  assert property (disable iff (rst)
                   (!ce && !$past(rst)) |-> (binary_count == $past(binary_count) &&
                                              gray_count   == $past(gray_count)));

  // Increment when ce=1
  assert property (disable iff (rst)
                   (ce && !$past(rst)) |-> (binary_count == $past(binary_count) + 1));

  // Gray output equals Gray(previous binary_count)
  assert property (disable iff (rst) (!$past(rst)) |->
                   (gray_count ==
                      { $past(binary_count[width-1]),
                        $past(binary_count[width-2:0]) ^ $past(binary_count[width-1:1]) }));

  // Consecutive enables toggle exactly one Gray bit
  assert property (disable iff (rst)
                   (ce && $past(ce) && !$past(rst)) |-> $onehot(gray_count ^ $past(gray_count)));

  // Coverage
  cover property (@(posedge rst) 1);
  cover property (disable iff (rst) (ce && $past(ce) && $onehot(gray_count ^ $past(gray_count))));
  cover property (disable iff (rst) (binary_count == '0));

endmodule