// SVA for multiplexer: concise, complete, and bind-ready

module multiplexer_sva #(parameter N = 1) (
  input  logic              ctrl,
  input  logic [N-1:0]      D0,
  input  logic [N-1:0]      D1,
  input  logic [N-1:0]      S
);

  // Functional correctness for known control
  assert property (@(*) (ctrl === 1'b0) |-> (S === D0))
    else $error("mux: ctrl==0 but S != D0");
  assert property (@(*) (ctrl === 1'b1) |-> (S === D1))
    else $error("mux: ctrl==1 but S != D1");

  // If inputs identical (including X/Z), output must match them
  assert property (@(*) (D0 === D1) |-> (S === D0))
    else $error("mux: D0===D1 but S mismatches");

  // Bit-accurate X-merge semantics when ctrl is X/Z
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_xmerge
      // Equal bits propagate
      assert property (@(*) ((ctrl !== 1'b0 && ctrl !== 1'b1) && (D0[i] === D1[i])) |-> (S[i] === D0[i]))
        else $error("mux: ctrl X/Z, D0[%0d]===D1[%0d], but S[%0d] != that value", i,i,i);
      // Different bits must yield X
      assert property (@(*) ((ctrl !== 1'b0 && ctrl !== 1'b1) && (D0[i] !== D1[i])) |-> $isunknown(S[i]))
        else $error("mux: ctrl X/Z, D0[%0d]!=D1[%0d], but S[%0d] not X", i,i,i);
    end
  endgenerate

  // Sanity: no X on S when selected input is known
  assert property (@(*) (ctrl === 1'b0 && !$isunknown(D0)) |-> (!$isunknown(S) && S === D0));
  assert property (@(*) (ctrl === 1'b1 && !$isunknown(D1)) |-> (!$isunknown(S) && S === D1));

  // Coverage
  cover property (@(*) ctrl === 1'b0 && S === D0);
  cover property (@(*) ctrl === 1'b1 && S === D1);
  cover property (@(*) (ctrl !== 1'b0 && ctrl !== 1'b1)); // exercise X/Z control
  generate
    for (i = 0; i < N; i++) begin : g_cov
      cover property (@(*) (ctrl === 1'b0) && (S[i] === 1'b0));
      cover property (@(*) (ctrl === 1'b0) && (S[i] === 1'b1));
      cover property (@(*) (ctrl === 1'b1) && (S[i] === 1'b0));
      cover property (@(*) (ctrl === 1'b1) && (S[i] === 1'b1));
    end
  endgenerate

endmodule

bind multiplexer multiplexer_sva #(.N(N)) u_multiplexer_sva (.*);