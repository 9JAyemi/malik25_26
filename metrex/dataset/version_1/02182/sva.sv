// SVA checkers (bind into DUT). Concise, high-signal-coverage.

////////////////////////////////////////////////////////////
// edge_detection assertions
////////////////////////////////////////////////////////////
module edge_detection_sva;
  default clocking cb @(posedge clk); endclocking

  // While in reset
  assert property (!rst_n |-> (rise==0 && fall==0 && prev_signal==0));

  // No simultaneous rise & fall
  assert property (disable iff (!rst_n) !(rise && fall));

  // prev_signal tracks prior signal; exact edge semantics; single-cycle pulses
  assert property (disable iff (!rst_n || !$past(rst_n)) prev_signal == $past(signal));

  assert property (disable iff (!rst_n || !$past(rst_n)) rise |-> (signal && !$past(signal)));
  assert property (disable iff (!rst_n || !$past(rst_n)) (signal && !$past(signal)) |-> rise);

  assert property (disable iff (!rst_n || !$past(rst_n)) fall |-> (!signal && $past(signal)));
  assert property (disable iff (!rst_n || !$past(rst_n)) (!signal && $past(signal)) |-> fall);

  assert property (disable iff (!rst_n) rise |=> !rise);
  assert property (disable iff (!rst_n) fall |=> !fall);

  // Coverage
  cover property (disable iff (!rst_n || !$past(rst_n)) rise);
  cover property (disable iff (!rst_n || !$past(rst_n)) fall);
  cover property (disable iff (!rst_n || !$past(rst_n))
                  (signal && !$past(signal)) ##1 (!signal && $past(signal)));
endmodule
bind edge_detection edge_detection_sva;


////////////////////////////////////////////////////////////
// minimum_finding assertions (combinational checks)
////////////////////////////////////////////////////////////
module minimum_finding_sva;
  // min_val must be a least element and sourced from inputs
  always @* begin
    assert (min_val <= a && min_val <= b && min_val <= c && min_val <= d)
      else $error("min_val not <= all inputs");

    assert (min_val==a || min_val==b || min_val==c || min_val==d)
      else $error("min_val not equal to any input");

    if ((a<b) && (a<c) && (a<d)) assert (min_val==a);
    if ((b<a) && (b<c) && (b<d)) assert (min_val==b);
    if ((c<a) && (c<b) && (c<d)) assert (min_val==c);
  end

  // Basic coverage (strict minima and a tie leading to 'd')
  always @* begin
    cover ((a<b)&&(a<c)&&(a<d) && (min_val==a));
    cover ((b<a)&&(b<c)&&(b<d) && (min_val==b));
    cover ((c<a)&&(c<b)&&(c<d) && (min_val==c));
    cover (((a==b)||(a==c)||(a==d)||(b==c)||(b==d)||(c==d)) && (min_val==d));
  end
endmodule
bind minimum_finding minimum_finding_sva;


////////////////////////////////////////////////////////////
// functional_module assertions
////////////////////////////////////////////////////////////
module functional_module_sva;
  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  assert property (!rst_n |-> (max_val==8'h00));

  // max_val update protocol
  assert property (disable iff (!rst_n) rise |=> max_val==8'hFF);
  assert property (disable iff (!rst_n) !rise |=> max_val==$past(max_val));

  // out next-state function (1-bit out reflects LSB of selected 8-bit source)
  assert property (disable iff (!rst_n || !$past(rst_n))
    1 |=> out == ( ($past(max_val) > $past(min_val)) ? $past(max_val[0])
                 : ($past(fall) ? $past(min_val[0]) : $past(out)) ));

  // Precedence when both conditions could fire (third if overrides)
  assert property (disable iff (!rst_n || !$past(rst_n))
    ($past(max_val) > $past(min_val)) |=> out == $past(max_val[0]));

  // Hold when neither condition applies
  assert property (disable iff (!rst_n || !$past(rst_n))
    (!$past(fall) && !($past(max_val) > $past(min_val))) |=> out == $past(out));

  // Optional: flag width-truncation risks when using 1-bit out
  assert property (disable iff (!rst_n || !$past(rst_n))
    ($past(max_val) > $past(min_val)) |-> $past(max_val[7:1])==0)
    else $error("Out truncates nonzero upper bits of max_val");
  assert property (disable iff (!rst_n || !$past(rst_n))
    ($past(fall) && !($past(max_val) > $past(min_val))) |-> $past(min_val[7:1])==0)
    else $error("Out truncates nonzero upper bits of min_val");

  // Coverage of key behaviors
  cover property (disable iff (!rst_n) rise ##1 (max_val==8'hFF));
  cover property (disable iff (!rst_n || !$past(rst_n))
    ($past(fall) && !($past(max_val) > $past(min_val))) ##1 (out == $past(min_val[0])));
  cover property (disable iff (!rst_n || !$past(rst_n))
    ($past(fall) && ($past(max_val) > $past(min_val))) ##1 (out == $past(max_val[0])));
  cover property (disable iff (!rst_n) rise && fall);
endmodule
bind functional_module functional_module_sva;


////////////////////////////////////////////////////////////
// top_module connectivity / integration assertions
////////////////////////////////////////////////////////////
module top_module_sva;
  default clocking cb @(posedge clk); endclocking

  // 'signal' captures LSB of 'a' (implicit truncation)
  assert property (disable iff (!rst_n || !$past(rst_n)) signal == $past(a[0]));

  // Sanity: downstream out is 1-bit; ensure it equals LSB of the selected value next-cycle
  // Re-express using internal fm context via hierarchical names if needed; kept minimal here.
endmodule
bind top_module top_module_sva;