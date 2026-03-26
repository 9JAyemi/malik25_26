module taxicab_distance_sva #(parameter N = 32) (
    input logic [N-1:0] x1,
    input logic [N-1:0] y1,
    input logic [N-1:0] x2,
    input logic [N-1:0] y2,
    input logic [N+1:0] dist
);

    function automatic logic signed [N:0] abs_diff_rtl (
        input logic [N-1:0] a,
        input logic [N-1:0] b
    );
        logic signed [N:0] d_ab;
        logic signed [N:0] d_ba;
        begin
            d_ab = a - b;
            d_ba = b - a;
            abs_diff_rtl = (a > b) ? d_ab : d_ba;
        end
    endfunction

    function automatic logic [N+1:0] dist_rtl (
        input logic [N-1:0] fx1,
        input logic [N-1:0] fy1,
        input logic [N-1:0] fx2,
        input logic [N-1:0] fy2
    );
        logic signed [N:0] xabs;
        logic signed [N:0] yabs;
        begin
            xabs = abs_diff_rtl(fx1, fx2);
            yabs = abs_diff_rtl(fy1, fy2);
            dist_rtl = xabs + yabs;
        end
    endfunction

    function automatic logic [N+1:0] branch_dist_x1_gt_x2_y1_gt_y2 (
        input logic [N-1:0] fx1,
        input logic [N-1:0] fy1,
        input logic [N-1:0] fx2,
        input logic [N-1:0] fy2
    );
        logic signed [N:0] dx;
        logic signed [N:0] dy;
        begin
            dx = fx1 - fx2;
            dy = fy1 - fy2;
            branch_dist_x1_gt_x2_y1_gt_y2 = dx + dy;
        end
    endfunction

    function automatic logic [N+1:0] branch_dist_x1_gt_x2_y1_le_y2 (
        input logic [N-1:0] fx1,
        input logic [N-1:0] fy1,
        input logic [N-1:0] fx2,
        input logic [N-1:0] fy2
    );
        logic signed [N:0] dx;
        logic signed [N:0] dy;
        begin
            dx = fx1 - fx2;
            dy = fy2 - fy1;
            branch_dist_x1_gt_x2_y1_le_y2 = dx + dy;
        end
    endfunction

    function automatic logic [N+1:0] branch_dist_x1_le_x2_y1_gt_y2 (
        input logic [N-1:0] fx1,
        input logic [N-1:0] fy1,
        input logic [N-1:0] fx2,
        input logic [N-1:0] fy2
    );
        logic signed [N:0] dx;
        logic signed [N:0] dy;
        begin
            dx = fx2 - fx1;
            dy = fy1 - fy2;
            branch_dist_x1_le_x2_y1_gt_y2 = dx + dy;
        end
    endfunction

    function automatic logic [N+1:0] branch_dist_x1_le_x2_y1_le_y2 (
        input logic [N-1:0] fx1,
        input logic [N-1:0] fy1,
        input logic [N-1:0] fx2,
        input logic [N-1:0] fy2
    );
        logic signed [N:0] dx;
        logic signed [N:0] dy;
        begin
            dx = fx2 - fx1;
            dy = fy2 - fy1;
            branch_dist_x1_le_x2_y1_le_y2 = dx + dy;
        end
    endfunction

    // No clock or reset exists in the RTL; sample on the formal global clock.

    // Output matches the implemented combinational arithmetic.
    check_dist_matches_rtl: assert property (
        @($global_clock) dist == dist_rtl(x1, y1, x2, y2)
    );

    // Identical points produce zero distance.
    check_zero_when_points_equal: assert property (
        @($global_clock) ((x1 == x2) && (y1 == y2)) |-> (dist == '0)
    );

    // Equal x coordinates leave only the y-axis difference.
    check_y_only_when_x_equal: assert property (
        @($global_clock) (x1 == x2) |-> (dist == dist_rtl({N{1'b0}}, y1, {N{1'b0}}, y2))
    );

    // Equal y coordinates leave only the x-axis difference.
    check_x_only_when_y_equal: assert property (
        @($global_clock) (y1 == y2) |-> (dist == dist_rtl(x1, {N{1'b0}}, x2, {N{1'b0}}))
    );

    // When x1>x2 and y1>y2, both forward differences are selected.
    check_branch_x1_gt_x2_y1_gt_y2: assert property (
        @($global_clock) ((x1 > x2) && (y1 > y2)) |-> (dist == branch_dist_x1_gt_x2_y1_gt_y2(x1, y1, x2, y2))
    );

    // When x1>x2 and y1<=y2, x forward and y reverse differences are selected.
    check_branch_x1_gt_x2_y1_le_y2: assert property (
        @($global_clock) ((x1 > x2) && (y1 <= y2)) |-> (dist == branch_dist_x1_gt_x2_y1_le_y2(x1, y1, x2, y2))
    );

    // When x1<=x2 and y1>y2, x reverse and y forward differences are selected.
    check_branch_x1_le_x2_y1_gt_y2: assert property (
        @($global_clock) ((x1 <= x2) && (y1 > y2)) |-> (dist == branch_dist_x1_le_x2_y1_gt_y2(x1, y1, x2, y2))
    );

    // When x1<=x2 and y1<=y2, both reverse differences are selected.
    check_branch_x1_le_x2_y1_le_y2: assert property (
        @($global_clock) ((x1 <= x2) && (y1 <= y2)) |-> (dist == branch_dist_x1_le_x2_y1_le_y2(x1, y1, x2, y2))
    );

    // Swapping the two endpoints leaves the computed distance unchanged.
    check_endpoint_swap_symmetry: assert property (
        @($global_clock) dist == dist_rtl(x2, y2, x1, y1)
    );

    // Swapping x and y roles leaves the computed distance unchanged.
    check_axis_swap_symmetry: assert property (
        @($global_clock) dist == dist_rtl(y1, x1, y2, x2)
    );

endmodule