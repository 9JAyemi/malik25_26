// SVA for FSM. Bind this module to the DUT instance.
module FSM_sva #(parameter int n=2, m=2, s=4)
(
  input logic               clk,
  input logic               rst,
  input logic [m-1:0]       in,
  input logic [n-1:0]       out,
  input logic [s-1:0]       state
);

  // helpers
  function automatic logic [2:0] f_next3 (input logic [2:0] ps, input logic [m-1:0] i);
    unique case (ps)
      3'b000: f_next3 = i[0] ? (i[1] ? 3'b010 : 3'b001) : 3'b000;
      3'b010: f_next3 = i[1] ? 3'b100 : 3'b011;
      3'b011: f_next3 = i[0] ? 3'b000 : 3'b010;
      3'b100: f_next3 = i[1] ? (i[0] ? 3'b110 : 3'b101) : 3'b100;
      3'b101: f_next3 = i[0] ? 3'b011 : 3'b100;
      3'b110: f_next3 = i[0] ? 3'b001 : (i[1] ? 3'b111 : 3'b110);
      3'b111: f_next3 = (i[0] && i[1]) ? 3'b010 : 3'b110;
      default: f_next3 = 3'b000;
    endcase
  endfunction

  function automatic logic [s-1:0] f_pack3 (input logic [2:0] x);
    return {{(s-3){1'b0}}, x};
  endfunction

  localparam logic [s-1:0] S000 = f_pack3(3'b000);
  localparam logic [s-1:0] S001 = f_pack3(3'b001);
  localparam logic [s-1:0] S010 = f_pack3(3'b010);
  localparam logic [s-1:0] S011 = f_pack3(3'b011);
  localparam logic [s-1:0] S100 = f_pack3(3'b100);
  localparam logic [s-1:0] S101 = f_pack3(3'b101);
  localparam logic [s-1:0] S110 = f_pack3(3'b110);
  localparam logic [s-1:0] S111 = f_pack3(3'b111);

  // Assertions

  // reset behavior and legal encoding
  assert property (@(posedge clk) rst |-> (state == S000));
  assert property (@(posedge clk) !$isunknown(state));
  assert property (@(posedge clk) state[s-1:3] == '0);

  // next-state function
  assert property (@(posedge clk) disable iff (rst || $past(rst))
                   state == f_pack3( f_next3($past(state[2:0]), $past(in)) ));

  // outputs are a pure function of state, no X
  assert property (@(posedge clk) disable iff (rst) !$isunknown(out));
  assert property (@(posedge clk) disable iff (rst)
    (state[2:0]!=3'b000 || out==2'b00) &&
    (state[2:0]!=3'b001 || out==2'b01) &&
    (state[2:0]!=3'b010 || out==2'b10) &&
    (state[2:0]!=3'b011 || out==2'b11) &&
    (state[2:0]!=3'b100 || out==2'b01) &&
    (state[2:0]!=3'b101 || out==2'b10) &&
    (state[2:0]!=3'b110 || out==2'b11) &&
    (state[2:0]!=3'b111 || out==2'b00)
  );

  // out stability when state stable
  assert property (@(posedge clk) disable iff (rst) $stable(state) |-> $stable(out));

  // Coverage: reachability of all states
  cover property (@(posedge clk) disable iff (rst) state==S000);
  cover property (@(posedge clk) disable iff (rst) state==S001);
  cover property (@(posedge clk) disable iff (rst) state==S010);
  cover property (@(posedge clk) disable iff (rst) state==S011);
  cover property (@(posedge clk) disable iff (rst) state==S100);
  cover property (@(posedge clk) disable iff (rst) state==S101);
  cover property (@(posedge clk) disable iff (rst) state==S110);
  cover property (@(posedge clk) disable iff (rst) state==S111);

  // Coverage: every legal transition (uses $past for input conditions)
  // From S000
  cover property (@(posedge clk) disable iff (rst || $past(rst))
                  ($past(state)==S000) && $past(in[0] && in[1]) && (state==S010));
  cover property (@(posedge clk) disable iff (rst || $past(rst))
                  ($past(state)==S000) && $past(in[0] && !in[1]) && (state==S001));
  cover property (@(posedge clk) disable iff (rst || $past(rst))
                  ($past(state)==S000) && $past(!in[0]) && (state==S000));
  // From S010
  cover property (@(posedge clk) disable iff (rst || $past(rst))
                  ($past(state)==S010) && $past(in[1]) && (state==S100));
  cover property (@(posedge clk) disable iff (rst || $past(rst))
                  ($past(state)==S010) && $past(!in[1]) && (state==S011));
  // From S011
  cover property (@(posedge clk) disable iff (rst || $past(rst))
                  ($past(state)==S011) && $past(in[0]) && (state==S000));
  cover property (@(posedge clk) disable iff (rst || $past(rst))
                  ($past(state)==S011) && $past(!in[0]) && (state==S010));
  // From S100
  cover property (@(posedge clk) disable iff (rst || $past(rst))
                  ($past(state)==S100) && $past(in[0] && in[1]) && (state==S110));
  cover property (@(posedge clk) disable iff (rst || $past(rst))
                  ($past(state)==S100) && $past(!in[0] && in[1]) && (state==S101));
  cover property (@(posedge clk) disable iff (rst || $past(rst))
                  ($past(state)==S100) && $past(!in[1]) && (state==S100));
  // From S101
  cover property (@(posedge clk) disable iff (rst || $past(rst))
                  ($past(state)==S101) && $past(in[0]) && (state==S011));
  cover property (@(posedge clk) disable iff (rst || $past(rst))
                  ($past(state)==S101) && $past(!in[0]) && (state==S100));
  // From S110
  cover property (@(posedge clk) disable iff (rst || $past(rst))
                  ($past(state)==S110) && $past(in[0]) && (state==S001));
  cover property (@(posedge clk) disable iff (rst || $past(rst))
                  ($past(state)==S110) && $past(!in[0] && in[1]) && (state==S111));
  cover property (@(posedge clk) disable iff (rst || $past(rst))
                  ($past(state)==S110) && $past(!in[1] && !in[0]) && (state==S110));
  // From S111
  cover property (@(posedge clk) disable iff (rst || $past(rst))
                  ($past(state)==S111) && $past(in[0] && in[1]) && (state==S010));
  cover property (@(posedge clk) disable iff (rst || $past(rst))
                  ($past(state)==S111) && $past(!(in[0] && in[1])) && (state==S110));

endmodule

// Example bind (adjust instance path as needed):
// bind FSM FSM_sva #(.n(n), .m(m), .s(s)) fsm_sva_i (.clk(clk), .rst(rst), .in(in), .out(out), .state(state));