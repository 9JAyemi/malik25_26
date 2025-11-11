// SVA for arbitrator
// Bind into DUT: bind arbitrator arbitrator_sva arb_sva();

module arbitrator_sva;

  // Mirror state encodings (keep in sync with DUT)
  localparam logic [3:0] REQUEST0     = 4'b0000;
  localparam logic [3:0] REQUEST1     = 4'b0001;
  localparam logic [3:0] REQUEST2     = 4'b0010;
  localparam logic [3:0] REQUEST3     = 4'b0011;
  localparam logic [3:0] REQUEST4     = 4'b0100;
  localparam logic [3:0] REQUEST5     = 4'b0101;
  localparam logic [3:0] WAIT_RELEASE = 4'b0110;
  localparam logic [3:0] WAIT_CYCLES  = 4'b0111;
  localparam logic [3:0] FINISH       = 4'b1111;

  // Convenience vectors
  wire [5:0] req      = {request5, request4, request3, request2, request1, request0};
  wire [5:0] rel      = {release5, release4, release3, release2, release1, release0};
  wire [5:0] permit_v = {permit5,  permit4,  permit3,  permit2,  permit1,  permit0};

  // ---------- Basic invariants ----------
  // Reset state on any clock while reset is low
  assert property (@(posedge clk) !reset |-> (state==REQUEST0 && permit_v==6'b0 && count==3'd0 && index==REQUEST0));

  // Legal encodings
  assert property (@(posedge clk) disable iff(!reset)
                   state inside {REQUEST0,REQUEST1,REQUEST2,REQUEST3,REQUEST4,REQUEST5,WAIT_RELEASE,WAIT_CYCLES,FINISH});
  assert property (@(posedge clk) disable iff(!reset)
                   index inside {REQUEST0,REQUEST1,REQUEST2,REQUEST3,REQUEST4,REQUEST5});

  // Permits: at most one high (or none)
  assert property (@(posedge clk) disable iff(!reset) $onehot0(permit_v));

  // If any permit is high, FSM must be in WAIT_RELEASE
  assert property (@(posedge clk) disable iff(!reset) (|permit_v) |-> (state==WAIT_RELEASE));

  // Count never exceeds terminal value
  assert property (@(posedge clk) disable iff(!reset) count <= 3'd4);

  // ---------- Request states: progress/grant semantics ----------
  // REQUEST0
  assert property (@(posedge clk) disable iff(!reset)
                   (state==REQUEST0 && !request0) |=> state==REQUEST1);
  assert property (@(posedge clk) disable iff(!reset)
                   (state==REQUEST0 &&  request0) |=> (state==WAIT_RELEASE && permit0 && index==REQUEST1));

  // REQUEST1
  assert property (@(posedge clk) disable iff(!reset)
                   (state==REQUEST1 && !request1) |=> state==REQUEST2);
  assert property (@(posedge clk) disable iff(!reset)
                   (state==REQUEST1 &&  request1) |=> (state==WAIT_RELEASE && permit1 && index==REQUEST2));

  // REQUEST2
  assert property (@(posedge clk) disable iff(!reset)
                   (state==REQUEST2 && !request2) |=> state==REQUEST3);
  assert property (@(posedge clk) disable iff(!reset)
                   (state==REQUEST2 &&  request2) |=> (state==WAIT_RELEASE && permit2 && index==REQUEST3));

  // REQUEST3
  assert property (@(posedge clk) disable iff(!reset)
                   (state==REQUEST3 && !request3) |=> state==REQUEST4);
  assert property (@(posedge clk) disable iff(!reset)
                   (state==REQUEST3 &&  request3) |=> (state==WAIT_RELEASE && permit3 && index==REQUEST4));

  // REQUEST4
  assert property (@(posedge clk) disable iff(!reset)
                   (state==REQUEST4 && !request4) |=> state==REQUEST5);
  assert property (@(posedge clk) disable iff(!reset)
                   (state==REQUEST4 &&  request4) |=> (state==WAIT_RELEASE && permit4 && index==REQUEST5));

  // REQUEST5
  assert property (@(posedge clk) disable iff(!reset)
                   (state==REQUEST5 && !request5) |=> state==REQUEST0);
  assert property (@(posedge clk) disable iff(!reset)
                   (state==REQUEST5 &&  request5) |=> (state==WAIT_RELEASE && permit5 && index==REQUEST0));

  // ---------- WAIT_RELEASE behavior ----------
  // No release: hold permits stable and remain in WAIT_RELEASE
  assert property (@(posedge clk) disable iff(!reset)
                   (state==WAIT_RELEASE && !(|rel)) |=> (state==WAIT_RELEASE && $stable(permit_v)));

  // Any release: clear permits, zero count, go to WAIT_CYCLES
  assert property (@(posedge clk) disable iff(!reset)
                   (state==WAIT_RELEASE &&  (|rel)) |=> (state==WAIT_CYCLES && permit_v==6'b0 && count==3'd0));

  // ---------- WAIT_CYCLES timing ----------
  // Increment until 4, stay in WAIT_CYCLES
  assert property (@(posedge clk) disable iff(!reset)
                   (state==WAIT_CYCLES && count!=3'd4) |=> (state==WAIT_CYCLES && count==$past(count)+3'd1));

  // When count hits 4, next is FINISH
  assert property (@(posedge clk) disable iff(!reset)
                   (state==WAIT_CYCLES && count==3'd4) |=> state==FINISH);

  // ---------- FINISH ----------
  // FINISH lasts one cycle and goes to 'index'; permits must remain 0
  assert property (@(posedge clk) disable iff(!reset)
                   (state==FINISH) |-> (permit_v==6'b0));
  assert property (@(posedge clk) disable iff(!reset)
                   (state==FINISH) |=> (state==index));

  // ---------- Coverage ----------
  // Cover a grant for each channel
  cover property (@(posedge clk) disable iff(!reset) (state==REQUEST0 && request0) |=> (state==WAIT_RELEASE && permit0));
  cover property (@(posedge clk) disable iff(!reset) (state==REQUEST1 && request1) |=> (state==WAIT_RELEASE && permit1));
  cover property (@(posedge clk) disable iff(!reset) (state==REQUEST2 && request2) |=> (state==WAIT_RELEASE && permit2));
  cover property (@(posedge clk) disable iff(!reset) (state==REQUEST3 && request3) |=> (state==WAIT_RELEASE && permit3));
  cover property (@(posedge clk) disable iff(!reset) (state==REQUEST4 && request4) |=> (state==WAIT_RELEASE && permit4));
  cover property (@(posedge clk) disable iff(!reset) (state==REQUEST5 && request5) |=> (state==WAIT_RELEASE && permit5));

  // Cover full post-release wait timing: 0..4 then FINISH
  cover property (@(posedge clk) disable iff(!reset)
    (state==WAIT_RELEASE && (|rel)) ##1
    (state==WAIT_CYCLES && count==3'd0) ##1
    (state==WAIT_CYCLES && count==3'd1) ##1
    (state==WAIT_CYCLES && count==3'd2) ##1
    (state==WAIT_CYCLES && count==3'd3) ##1
    (state==WAIT_CYCLES && count==3'd4) ##1
    (state==FINISH));

  // Cover rotation: grant on 0 then, after release/wait, we reach REQUEST1
  cover property (@(posedge clk) disable iff(!reset)
    (state==REQUEST0 && request0) ##1
    (state==WAIT_RELEASE && permit0) ##1
    (state==WAIT_CYCLES && count==3'd0) ##1
    (state==WAIT_CYCLES && count==3'd4) ##1
    (state==FINISH) ##1
    (state==REQUEST1));

endmodule

bind arbitrator arbitrator_sva arb_sva();