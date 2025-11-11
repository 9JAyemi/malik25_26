// SVA checker for vending_machine
module vending_machine_sva
  #(parameter WAIT=2'd0, INSERTED=2'd1, DISPENSED=2'd2)
(
  input  logic        clk,
  input  logic        reset,
  input  logic        quarter,
  input  logic        button_a,
  input  logic        button_b,
  input  logic        button_c,
  input  logic        dispense,
  input  logic        product_a,
  input  logic        product_b,
  input  logic        product_c,
  input  logic [1:0]  state,
  input  logic [1:0]  product
);

  default clocking cb @(posedge clk); endclocking
  // Reset checks (synchronous)
  assert property (@(posedge clk) reset |=> state==WAIT && product==2'b00 &&
                                    !dispense && !product_a && !product_b && !product_c)
    else $error("Reset did not drive DUT to known idle state");

  // All other checks disabled during reset
  default disable iff (reset);

  // State encoding is legal
  assert property (state inside {WAIT, INSERTED, DISPENSED})
    else $error("Illegal state encoding");

  // WAIT state behavior and button priority
  assert property (state==WAIT && button_a |=> state==INSERTED && product==2'b01)
    else $error("WAIT: button_a did not select product_a/INSERTED");
  assert property (state==WAIT && !button_a && button_b |=> state==INSERTED && product==2'b10)
    else $error("WAIT: button_b did not select product_b/INSERTED");
  assert property (state==WAIT && !button_a && !button_b && button_c |=> state==INSERTED && product==2'b11)
    else $error("WAIT: button_c did not select product_c/INSERTED");
  assert property (state==WAIT && !(button_a||button_b||button_c) |=> state==WAIT && $stable(product))
    else $error("WAIT: unexpected transition/change without button");
  assert property (state==WAIT |=> state!=DISPENSED)
    else $error("WAIT: illegal direct transition to DISPENSED");

  // INSERTED state behavior
  assert property (state==INSERTED |-> product inside {2'b01,2'b10,2'b11})
    else $error("INSERTED: product must be valid non-zero choice");
  assert property (state==INSERTED |-> $stable(product))
    else $error("INSERTED: product changed unexpectedly");
  assert property (state==INSERTED && !quarter |=> state==INSERTED)
    else $error("INSERTED: advanced without quarter");
  assert property (state==INSERTED && quarter && (product inside {2'b01,2'b10,2'b11}) |=> state==DISPENSED)
    else $error("INSERTED: did not advance to DISPENSED on quarter");

  // DISPENSED state behavior and outputs
  assert property (state==DISPENSED |=> state==WAIT)
    else $error("DISPENSED: did not return to WAIT next cycle");
  assert property (state==DISPENSED |-> product inside {2'b01,2'b10,2'b11})
    else $error("DISPENSED: invalid product code");
  assert property (state==DISPENSED |-> dispense)
    else $error("DISPENSED: dispense not asserted");
  assert property (state==DISPENSED |-> (product==2'b01) -> ( product_a && !product_b && !product_c))
    else $error("DISPENSED: product_a output mismatch");
  assert property (state==DISPENSED |-> (product==2'b10) -> (!product_a &&  product_b && !product_c))
    else $error("DISPENSED: product_b output mismatch");
  assert property (state==DISPENSED |-> (product==2'b11) -> (!product_a && !product_b &&  product_c))
    else $error("DISPENSED: product_c output mismatch");

  // Outputs should only assert in DISPENSED and be one-hot-or-zero
  assert property ((dispense || product_a || product_b || product_c) |-> state==DISPENSED)
    else $error("Outputs asserted outside DISPENSED");
  assert property ($onehot0({product_a,product_b,product_c}))
    else $error("Product outputs not one-hot");

  // Outputs should be single-cycle pulses (expected behavior)
  assert property (state==DISPENSED |=> !dispense && !product_a && !product_b && !product_c)
    else $error("Outputs did not deassert after DISPENSED");

  // Functional coverage
  cover property (state==WAIT && button_a ##1 state==INSERTED ##1 quarter
                  ##1 state==DISPENSED && dispense && product_a);
  cover property (state==WAIT && !button_a && button_b ##1 state==INSERTED ##1 quarter
                  ##1 state==DISPENSED && dispense && product_b);
  cover property (state==WAIT && !button_a && !button_b && button_c ##1 state==INSERTED ##1 quarter
                  ##1 state==DISPENSED && dispense && product_c);
  // Priority cover: simultaneous buttons pick A
  cover property (state==WAIT && button_a && button_b ##1 state==INSERTED && product==2'b01);

endmodule

// Bind to DUT (connect internal regs state/product)
bind vending_machine vending_machine_sva
  #(.WAIT(WAIT), .INSERTED(INSERTED), .DISPENSED(DISPENSED))
  vm_sva_i(
    .clk(clk),
    .reset(reset),
    .quarter(quarter),
    .button_a(button_a),
    .button_b(button_b),
    .button_c(button_c),
    .dispense(dispense),
    .product_a(product_a),
    .product_b(product_b),
    .product_c(product_c),
    .state(state),
    .product(product)
  );