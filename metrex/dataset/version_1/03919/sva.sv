// Assertions/coverage for the given design
// Bind this file alongside the DUT

// Priority encoder checks (structural + sanity)
module priority_encoder_sva;
  // Compile-time width sanity (flags current bug)
  initial begin
    if ($bits({a,b,c,d}) != $bits(temp))
      $error("priority_encoder: width mismatch: temp[%0d] != {a,b,c,d}[%0d]",
             $bits(temp), $bits({a,b,c,d}));
  end
  // No X/Z on index
  always @* assert (!$isunknown(index)) else
    $error("priority_encoder: index has X/Z");
endmodule


// Min-decade counter functional checks
module min_decade_counter_sva;
  // Reset drives counter to 0 (synchronous)
  assert property (@(posedge clk) reset |-> counter==4'd0);

  // q mirrors counter
  assert property (@(posedge clk) q==counter);

  // Hold when CE=0
  assert property (@(posedge clk) disable iff (reset)
                   !clock_enable |=> counter==$past(counter));

  // Count up when CE=1 (non-9)
  assert property (@(posedge clk) disable iff (reset)
                   clock_enable && $past(counter)!=4'd9 |=> counter==$past(counter)+1);

  // Wrap to 0 at 9 when CE=1
  assert property (@(posedge clk) disable iff (reset)
                   clock_enable && $past(counter)==4'd9 |=> counter==4'd0);

  // min selection mapping by index
  assert property (@(posedge clk) index==3'd0 |-> min==a);
  assert property (@(posedge clk) index==3'd1 |-> min==b);
  assert property (@(posedge clk) index==3'd2 |-> min==c);
  assert property (@(posedge clk) index==3'd3 |-> min==d);
  assert property (@(posedge clk) index>=3'd4 |-> min==8'h00);

  // No X/Z on key outputs
  assert property (@(posedge clk) disable iff (reset) !$isunknown({min,q,counter}));

  // Coverage: wrap, reach all counts, all index cases
  cover property (@(posedge clk) disable iff (reset)
                  clock_enable ##1 counter==4'd9 ##1 counter==4'd0);

  genvar ci;
  generate
    for (ci=0; ci<=9; ci++) begin : cov_counts
      cover property (@(posedge clk) counter==ci);
    end
  endgenerate

  cover property (@(posedge clk) index==3'd0 && min==a);
  cover property (@(posedge clk) index==3'd1 && min==b);
  cover property (@(posedge clk) index==3'd2 && min==c);
  cover property (@(posedge clk) index==3'd3 && min==d);
  cover property (@(posedge clk) index>=3'd4 && min==8'h00);
endmodule


// Top-level gating checks
module top_module_sva;
  // select=0 forces zeros on outputs
  assert property (@(posedge clk) select==1'b0 |-> min==8'h00 && q==4'h0);

  // select=1 passes through internal values
  assert property (@(posedge clk) select==1'b1 |-> min==min_value && q==counter_value);

  // No X/Z on outputs
  assert property (@(posedge clk) !$isunknown({min,q}));

  // Coverage: both select states
  cover property (@(posedge clk) select==1'b0);
  cover property (@(posedge clk) select==1'b1);
endmodule


// Bind assertions to DUT
bind priority_encoder    priority_encoder_sva   pe_sva();
bind min_decade_counter  min_decade_counter_sva mdc_sva();
bind top_module          top_module_sva         top_sva();