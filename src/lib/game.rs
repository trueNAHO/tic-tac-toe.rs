use inquire::{required, validator::Validation, CustomType, InquireError, Select, Text};
use itertools::Itertools;
use prettytable::Table;
use sm::sm;
use tap::Pipe;

use crate::{
    board::{Board, BoardState},
    player::Player,
    player_index::PlayerIndex,
    players::Players,
};

sm! {
    GameState {
        InitialStates { Running }

        GameDraw { Running => Draw }
        GameWin { Running => Won }
    }
}

/// The [Tic-tac-toe] game that consists of a [`Board`] and [`Players`].
///
/// [Tic-tac-toe]: https://en.wikipedia.org/wiki/Tic-tac-toe
/// [`Board`]: crate::board::Board
/// [`Players`]: crate::players::Players
pub struct Game;

impl Game {
    /// Run the game.
    pub fn run() -> Result<(), InquireError> {
        let players = Game::players()?;
        let mut board = Game::board()?;

        let board_demo = (board.0.row_len())
            .pipe(|width| {
                (0..width)
                    .map(move |column| (0..width).map(move |element| element + column * width))
            })
            .pipe(Table::from_iter)
            .to_string();

        let mut players_cycle = players
            .0
            .iter()
            .enumerate()
            .map(|(index, player)| (PlayerIndex(index), player))
            .cycle();

        let mut game_state = GameState::Machine::new(GameState::Running).as_enum();

        let mut winner: Option<PlayerIndex> = None;

        while let GameState::Variant::InitialRunning(_) = game_state {
            let (player_index, player) = players_cycle.next().expect("Should be a cycle");

            Self::render(&board, &players, player.name.as_ref(), &board_demo);

            game_state = Self::input(&board)?.pipe(|board_size| {
                Self::update(
                    game_state,
                    &mut board,
                    player_index,
                    board_size,
                    &mut winner,
                )
            });
        }

        println!(
            "{}\n==== {} ====",
            board.display(&players),
            match game_state {
                GameState::Variant::DrawByGameDraw(_) => "DRAW!".into(),

                GameState::Variant::InitialRunning(_) =>
                    unreachable!("Otherwise loop should have continued"),

                GameState::Variant::WonByGameWin(_) => format!(
                    "{} WON!",
                    players
                        .0
                        .get(
                            winner
                                .expect("Winning the game should have set the winner")
                                .0
                        )
                        .expect(
                            "Player index should never go out of sync with the players collection"
                        )
                        .name
                ),
            }
        );

        Ok(())
    }
}

impl Game {
    fn board() -> Result<Board, InquireError> {
        CustomType::<usize>::new("Enter the board size:")
            .with_default(3)
            .with_formatter(&|input| format!("{0}x{0}", input))
            .with_help_message("For example, a board size of '3' results in a '3x3' grid.")
            .with_validator(|&input: &_| {
                Board::validate_new(input)
                    .and_then(|_| Validation::Valid.pipe(Ok))
                    .or_else(|error| Validation::Invalid(error.into()).pipe(Ok))
            })
            .prompt()?
            .pipe(|input| Board::new(input).expect("User input should yield a valid board size"))
            .pipe(Ok)
    }

    fn input(board: &Board) -> Result<usize, InquireError> {
        Select::new(
            "Enter board index:",
            board
                .0
                .elements_row_major_iter()
                .enumerate()
                .filter_map(|(index, element)| element.is_none().then_some(index))
                .collect_vec(),
        )
        .prompt()?
        .pipe(Ok)
    }

    fn players() -> Result<Players, InquireError> {
        CustomType::<usize>::new("Enter the player count:")
            .with_default(2)
            .with_help_message("Game turns cycle among players")
            .with_validator(|&input: &_| {
                (input >= 1)
                    .then(|| Validation::Valid.pipe(Ok))
                    .unwrap_or_else(|| {
                        Validation::Invalid("Requires at least one player".into()).pipe(Ok)
                    })
            })
            .prompt()?
            .pipe(|input| 1..=input)
            .map(|index| -> Result<Player, InquireError> {
                Player {
                    name: Text::new(format!("[Player {}] Enter your name:", index).as_str())
                        .with_validator(required!())
                        .prompt()?,
                    mark: Text::new(format!("[Player {}] Enter your mark:", index).as_str())
                        .with_validator(required!())
                        .prompt()?,
                }
                .pipe(Ok)
            })
            .collect::<Result<Vec<_>, _>>()?
            .pipe(Players)
            .pipe(Ok)
    }

    fn render(board: &Board, players: &Players, player_name: &str, board_demo: &str) {
        println!(
            "==> {}'s turn:\n\nThe board indexes are as follows:\n\n{}\nCurrently, the board is as follows:\n\n{}",
            player_name,
            board_demo,
            board.display(players),
        );
    }

    fn update(
        game_state: GameState::Variant,
        board: &mut Board,
        player_index: PlayerIndex,
        board_index: usize,
        winner: &mut Option<PlayerIndex>,
    ) -> GameState::Variant {
        match game_state {
            GameState::Variant::InitialRunning(state) => {
                board
                    .0
                    .set_row_major(board_index, player_index.pipe(Some))
                    .expect("User input should be in bound");

                match board.state() {
                    BoardState::Won(winner_index) => {
                        *winner = winner_index.to_owned().pipe(Some);
                        state.transition(GameState::GameWin).as_enum()
                    }
                    BoardState::Draw => state.transition(GameState::GameDraw).as_enum(),
                    BoardState::InProgress => state.as_enum(),
                }
            }

            _ => game_state,
        }
    }
}
