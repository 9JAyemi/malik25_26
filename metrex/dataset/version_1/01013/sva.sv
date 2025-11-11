// SVA checker for gray_code_state_machine
// Binds to internal state and output to verify mapping, next-state, reset, and recovery.
// Concise but high-quality checks plus targeted coverage.

module gray_code_state_machine_sva #(parameter int N = 4)
  (input logic                clk,
   input logic                rst,
   input logic [N-1:0]        state,
   input logic [N-1:0]        out);

  // Sanity on parameterization
  initial assert (N >= 3) else $error("N must be >= 3");

  // Combinational mapping (mirrors DUT intent; 0 for states >= 8)
  function automatic logic [N-1:0] map_gray(input logic [N-1:0] s);
    logic [N-1:0] r;
    r = '0;
    unique case (s[2:0])
      3'd0: r[2:0] = 3'd0;
      3'd1: r[2:0] = 3'd1;
      3'd2: r[2:0] = 3'd3;
      3'd3: r[2:0] = 3'd2;
      3'd4: r[2:0] = 3'd6;
      3'd5: r[2:0] = 3'd7;
      3'd6: r[2:0] = 3'd5;
      3'd7: r[2:0] = 3'd4;
    endcase
    return (s[N-1:3]=='0) ? r : '0;
  endfunction

  // No X/Z on observable state/out
  assert property (@(posedge clk) !$isunknown({state,out}));

  // Synchronous reset drives state and out to 0 on the next edge
  assert property (@(posedge clk) rst |=> (state=='0 && out=='0));

  // Out is always the combinational mapping of current state
  assert property (@(posedge clk) out == map_gray(state));

  // Next-state update follows mapping of previous state when not in reset
  assert property (@(posedge clk) !rst |=> state == map_gray($past(state)));

  // Illegal state (upper bits nonzero) must recover to 0 next cycle (when not in reset)
  assert property (@(posedge clk) !rst && (state[N-1:3] != '0) |=> state=='0);

  // If state is stable, out must be stable (pure combinational function)
  assert property (@(posedge clk) $stable(state) |-> $stable(out));

  // Coverage: observe each legal state 0..7
  cover property (@(posedge clk) disable iff (rst) state == {{(N-3){1'b0}},3'd0});
  cover property (@(posedge clk) disable iff (rst) state == {{(N-3){1'b0}},3'd1});
  cover property (@(posedge clk) disable iff (rst) state == {{(N-3){1'b0}},3'd2});
  cover property (@(posedge clk) disable iff (rst) state == {{(N-3){1'b0}},3'd3});
  cover property (@(posedge clk) disable iff (rst) state == {{(N-3){1'b0}},3'd4});
  cover property (@(posedge clk) disable iff (rst) state == {{(N-3){1'b0}},3'd5});
  cover property (@(posedge clk) disable iff (rst) state == {{(N-3){1'b0}},3'd6});
  cover property (@(posedge clk) disable iff (rst) state == {{(N-3){1'b0}},3'd7});

  // Coverage: exercise next-state mapping from each legal state
  genvar k;
  generate
    for (k=0; k<8; k++) begin : C_MAP
      localparam logic [N-1:0] K = {{(N-3){1'b0}},3'(k)};
      cover property (@(posedge clk) disable iff (rst) state==K ##1 state==map_gray(K));
    end
  endgenerate

  // Coverage: illegal state recovers to 0
  cover property (@(posedge clk) disable iff (rst) (state[N-1:3] != '0) ##1 state=='0);

endmodule

// Bind into DUT (example)
// bind gray_code_state_machine gray_code_state_machine_sva #(.N(n))
//   u_gray_code_state_machine_sva(.clk(clk), .rst(rst), .state(state), .out(out));