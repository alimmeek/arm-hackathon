module arbiter (
    input  logic clk,
    input  logic resetn,

    input  logic [2:0] r,
    
    output logic [2:0] g
);

parameter A = 2'b00, B = 2'b01, C = 2'b10, D = 2'b11;

logic [1:0] next_state;
logic [1:0] curr_state;

logic [2:0] g_next;
logic [2:0] g_q;

always_comb begin
    next_state = curr_state;
    case (curr_state)
        A : begin
            if (r[0]) begin
                next_state = B;
            end else if (r[1]) begin
                next_state = C;
            end else if (r[2]) begin
                next_state = D;
            end
        end

        B : begin
            if (~r[0]) begin
                next_state = A;
            end
        end

        C : begin
            if (~r[1]) begin
                next_state = A;
            end
        end

        D : begin
            if (~r[2]) begin
                next_state = A;
            end
        end
    endcase
end

always_comb begin
    g_next = g_q;
    case (next_state)
        A : g_next = 3'b000;

        B : g_next = 3'b001;

        C : g_next = 3'b010;

        D : g_next = 3'b100;
    endcase
end

always_ff @(posedge clk or negedge resetn) begin
    if (~resetn) begin
        curr_state <= A;
        g_q <= 3'b000;
    end else begin
        curr_state <= next_state;
        g_q <= g_next;
    end
end

assign g = g_q;



// Assertions

default clocking @(posedge clk);
endclocking

assert_a_to_b : assert property (((r[0]) && (curr_state == A)) |-> ##1 (curr_state == B));

assert_a_to_c : assert property (((r[1] && ~r[0]) && (curr_state == A)) |-> ##1 (curr_state == C));

assert_a_to_d : assert property (((r[2]&& ~r[0] && ~r[1]) && (curr_state == A)) |-> ##1 (curr_state == D));

assert_b_to_a : assert property (((~r[0]) && (curr_state == B)) |-> ##1 (curr_state == A));

assert_c_to_a : assert property (((~r[1]) && (curr_state == C)) |-> ##1 (curr_state == A));

assert_d_to_a : assert property (((~r[2]) && (curr_state == D)) |-> ##1 (curr_state == A));

assert_b_cant_go_to_c_or_d : assert property ((curr_state == B) |-> ((next_state != C) && (next_state != D)));

assert_c_cant_go_to_b_or_d : assert property ((curr_state == C) |-> ((next_state != B) && (next_state != D)));

assert_d_cant_go_to_b_or_c : assert property ((curr_state == D) |-> ((next_state != B) && (next_state != C)));

assert_g0_gets_set : assert property ((next_state == B) |-> ##1 (g[0] == 1'b1));

assert_g1_gets_set : assert property ((next_state == C) |-> ##1 (g[1] == 1'b1));

assert_g2_gets_set : assert property ((next_state == D) |-> ##1 (g[2] == 1'b1));

assert_only_one_granted : assert property ($onehot(g_q) || g_q == 3'b0);

endmodule